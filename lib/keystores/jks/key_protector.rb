require 'openssl'
require 'digest'
require 'securerandom'
require 'keystores/jks/pkcs8_key'
require 'keystores/jks/encrypted_private_key_info'
require 'javaobs'

# This is an implementation of a Sun proprietary, exportable algorithm
# intended for use when protecting (or recovering the cleartext version of)
# sensitive keys.
# This algorithm is not intended as a general purpose cipher.
#
# This is how the algorithm works for key protection:
# p - user password
# s - random salt
# X - xor key
# P - to-be-protected key
# Y - protected key
# R - what gets stored in the keystore
#
# Step 1:
# Take the user's password, append a random salt (of fixed size) to it,
# and hash it: d1 = digest(p, s)
# Store d1 in X.
#
# Step 2:
# Take the user's password, append the digest result from the previous step,
# and hash it: dn = digest(p, dn-1).
# Store dn in X (append it to the previously stored digests).
# Repeat this step until the length of X matches the length of the private key P.
#
# Step 3:
# XOR X and P, and store the result in Y: Y = X XOR P.
#
# Step 4:
# Store s, Y, and digest(p, P) in the result buffer R:
# R = s + Y + digest(p, P), where "+" denotes concatenation.
# (NOTE: digest(p, P) is stored in the result buffer, so that when the key is
# recovered, we can check if the recovered key indeed matches the original
# key.) R is stored in the keystore.
#
# The protected key is recovered as follows:
#
# Step1 and Step2 are the same as above, except that the salt is not randomly
# generated, but taken from the result R of step 4 (the first length(s)
# bytes).
#
# Step 3 (XOR operation) yields the plaintext key.
#
# Then concatenate the password with the recovered key, and compare with the
# last length(digest(p, P)) bytes of R. If they match, the recovered key is
# indeed the same key as the original key.
#
# TODO, implement this as an OpenSSL PBE Cipher
module Keystores
  module Jks
    class KeyProtector
      SALT_LEN = 20
      DIGEST_LEN = 20
      KEY_PROTECTOR_OID = '1.3.6.1.4.1.42.2.17.1.1'

      def initialize(password)
        @password = password
        @passwd_bytes = []
        password.unpack('c*').each do |byte|
          @passwd_bytes << (byte >> 8)
          @passwd_bytes << byte
        end
        @message_digest = OpenSSL::Digest::SHA1.new
      end

      def protect(key)
        if key.nil?
          raise ArgumentError.new("plaintext key can't be null")
        end

        plain_key = key.to_pkcs8_der.unpack('c*')

        # Determine the number of digest rounds
        num_rounds = plain_key.length / DIGEST_LEN
        num_rounds += 1 if (plain_key.length % DIGEST_LEN) != 0

        salt = SecureRandom.random_bytes(SALT_LEN)
        xor_key = Array.new(plain_key.length, 0)

        xor_offset = 0
        digest = salt

        # Compute the digests, and store them in xor_key
        for i in 1..num_rounds
          @message_digest.update(@passwd_bytes.pack('c*'))
          @message_digest.update(digest)
          digest = @message_digest.digest
          @message_digest.reset

          if i < num_rounds
            xor_key[xor_offset..(digest.length + xor_offset -1)] = digest.bytes
          else
            xor_key[xor_offset..-1] = digest[0..(xor_key.length - xor_offset - 1)].bytes
          end
          xor_offset += DIGEST_LEN
        end

        # XOR plain_key with xor_key, and store the result in tmpKey
        tmp_key = []
        for i in 0..(plain_key.length - 1)
          tmp_key[i] = plain_key[i] ^ xor_key[i]
        end

        # Store salt and tmp_key in encr_key
        encr_key = salt.unpack('c*') + tmp_key

        # Append digest(password, plain_key) as an integrity check to encr_key
        @message_digest << @passwd_bytes.pack('c*')
        @passwd_bytes.fill(0)
        @passwd_bytes = nil
        @message_digest << plain_key.pack('c*')
        digest = @message_digest.digest
        @message_digest.reset

        encr_key += digest.unpack('c*')
        Keystores::Jks::EncryptedPrivateKeyInfo.new(:algorithm => KEY_PROTECTOR_OID,
                                                    :encrypted_data => encr_key.pack('c*')).encoded
      end

      def unseal(sealed_object)
        raise ArgumentError.new("Unsupported algorithm used for encrypting SealedObject: #{sealed_object.seal_alg}") unless sealed_object.seal_alg == "PBEWithMD5AndTripleDES"
        raise ArgumentError.new("Unexpected parameters algorithm used, shoudl match #{sealed_object.seal_alg} but found #{sealed_object.params_alg}") unless sealed_object.seal_alg == sealed_object.params_alg
        raise ArgumentError.new("No parameters found in Sealed object for sealing algorithm. Need a salt and teration count to unseal.") unless !sealed_object.encoded_params.empty?

        params = sealed_object.encoded_params.map {|b| b.chr}.join
        decoded = OpenSSL::ASN1::decode(params)
        salt = decoded.value[0].value
        iteration_count = decoded.value[1].value.to_i

        plaintext = jce_pbe_decrypt(sealed_object.encrypted_content, @passwd_bytes, salt, iteration_count)
        stream = StringIO.new(plaintext)
        object_input_stream = Java::ObjectInputStream.new(stream)
        object_input_stream.readObject
      end

      def jce_pbe_decrypt(encrypted_content, password_bytes, salt, iteration_count)

        key, iv = jce_pbe_key_and_iv(salt, iteration_count)

        cipher = OpenSSL::Cipher::Cipher.new('des3')
        cipher.encrypt
        cipher.key = key
        cipher.iv =  iv
        cipher.decrypt
        encrypted_string = encrypted_content.map {|b| b.chr}.join

        plaintext = cipher.update(encrypted_string)
        plaintext << cipher.final
        return plaintext

      end

      def jce_pbe_key_and_iv(salt, iteration_count)
        raise ArgumentError.new("Expected 8 byte salt, found {salt.length} bytes") if salt.length != 8

        salt_halves = [salt[0..3], salt[4..8]]
        salt_halves[0] = jce_invert_salt_half(salt_halves[0]) if salt_halves[0] == salt_halves[1]

        derived = 2.times.map do |i|
          to_be_hashed = salt_halves[i]
          iteration_count.times do |j|
            md5 = Digest::MD5.new
            md5.update(to_be_hashed)
            md5.update(@password)
            to_be_hashed = md5.digest
          end
          to_be_hashed
        end.join

        key = derived[0..-9]
        iv = derived[-8..-1]
        return [key, iv]
      end

      def jce_invert_salt_half(salt_half)
        bytes = salt_half.bytes
        bytes[2] = bytes[1]
        bytes[1] = bytes[0]
        bytes[0] = bytes[3]
        bytes.map {|b| b.chr}.join
      end


      def recover(encrypted_private_key_info)
        unless encrypted_private_key_info.algorithm == KEY_PROTECTOR_OID
          raise IOError.new("Unsupported key protection algorithm: #{encrypted_private_key_info.algorithm}")
        end

        protected_key = encrypted_private_key_info.encrypted_data

        # Get the salt associated with this key (the first SALT_LEN bytes of protected_key)
        salt = protected_key.slice(0..(SALT_LEN - 1))

        # Determine the number of digest rounds
        encr_key_len = protected_key.length - SALT_LEN - DIGEST_LEN
        num_rounds = encr_key_len / DIGEST_LEN
        num_rounds += 1 if (encr_key_len % DIGEST_LEN) != 0

        # Get the encrypted key portion
        encr_key = protected_key.slice(SALT_LEN..(encr_key_len + SALT_LEN - 1))

        xor_key = Array.new(encr_key.size, 0)
        xor_offset = 0

        digest = salt
        # Compute the digests, and store them in xor_key
        for i in 1..num_rounds
          @message_digest.update(@passwd_bytes.pack('c*'))
          @message_digest.update(digest)
          digest = @message_digest.digest
          @message_digest.reset

          if i < num_rounds
            xor_key[xor_offset..(digest.length + xor_offset -1)] = digest.bytes
          else
            xor_key[xor_offset..-1] = digest[0..(xor_key.length - xor_offset - 1)].bytes
          end
          xor_offset += DIGEST_LEN
        end

        # XOR encr_key with xor_key, and store the result in plain_key
        plain_key = []
        encr_key_unpacked = encr_key.bytes

        for i in 0..(encr_key.size - 1)
          plain_key[i] = encr_key_unpacked[i] ^ xor_key[i]
        end

        # Check the integrity of the recovered key by concatenating it with
        # the password, digesting the concatenation, and comparing the
        # result of the digest operation with the digest provided at the end
        # of protected_key. If the two digest values are
        # * different, raise an error.
        @message_digest << @passwd_bytes.pack('c*')
        @passwd_bytes.fill(0)
        @passwd_bytes = nil
        @message_digest << plain_key.pack('c*')
        digest = @message_digest.digest
        @message_digest.reset

        for i in 0..(digest.length - 1)
          if digest[i] != protected_key[SALT_LEN + encr_key_len + i]
            raise IOError.new('Cannot recover key')
          end
        end
        OpenSSL::PKey.pkcs8_parse(plain_key.pack('c*'))
      end
    end
  end
end


