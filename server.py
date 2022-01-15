import socket,json
import time
import Crypto.Util.number
import Crypto.Random
import sys

print("#||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||#")
print()
print("                                                 Hashing SHA-512                                            ")
import hashlib
import sys

#round constants array
k = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538, 
    0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe, 
    0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 
    0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65, 
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab, 
    0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 
    0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 
    0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b, 
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218, 
    0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 
    0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 
    0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec, 
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c, 
    0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 
    0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 
    0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

def rot_right(x, c): #Right rotate for 64-bits numbers
    x &= 0xFFFFFFFFFFFFFFFF 
    return ((x >> c) | (x << (64 - c))) & 0xFFFFFFFFFFFFFFFF

def shift_left(x, c):
    return x << c

def shift_right(x, c):
    return x >> c

def sha512(text):

    hash0 = 0x6a09e667f3bcc908
    hash1 = 0xbb67ae8584caa73b
    hash2 = 0x3c6ef372fe94f82b
    hash3 = 0xa54ff53a5f1d36f1
    hash4 = 0x510e527fade682d1
    hash5 = 0x9b05688c2b3e6c1f
    hash6 = 0x1f83d9abfb41bd6b
    hash7 = 0x5be0cd19137e2179
    hashparts= [hash0, hash1, hash2, hash3, hash4, hash5, hash6, hash7]
    hash0, hash1, hash2, hash3, hash4, hash5, hash6, hash7 = hashparts
  
    data = bytearray(text)
    orig_bit_len = (8 * len(data)) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    data.append(0x80) #adding one byte at end of input

    while len(data) % 128 != 112: # padding zeros if input bits != 896 (mod 1024) 
        data.append(0)
    
    data += orig_bit_len.to_bytes(16, 'big') #append orig_bit_length mod (2^128)
  
    for offset in range(0, len(data), 128): #text processing in 128 byte blocks
    
        block = data[offset : offset + 128] #block of 128 bytes
        word = [0 for i in range(80)] 
    
        for i in range(16): # dividing blocks into first 16 8 bytes word
            word[i] = int.from_bytes(block[8*i : 8*i + 8],'big')
       
        for i in range(16, 80): #processing remaining 64 words
            s0 = (rot_right(word[i-15], 1) ^ rot_right(word[i-15], 8) ^ shift_right(word[i-15], 7)) & 0xFFFFFFFFFFFFFFFF
            s1 = (rot_right(word[i-2], 19) ^ rot_right(word[i-2], 61) ^ shift_right(word[i-2], 6)) & 0xFFFFFFFFFFFFFFFF
            word[i] = (word[i-16] + s0 + word[i-7] + s1) & 0xFFFFFFFFFFFFFFFF
        # hash value for 1st part
        a, b, c, d, e, f, g, h = hash0, hash1, hash2, hash3, hash4, hash5, hash6, hash7
        # loop for 80 rounds
        for i in range(80):
            S1 = (rot_right(e, 14) ^ rot_right(e, 18) ^ rot_right(e, 41)) & 0xFFFFFFFFFFFFFFFF
            ch = ((e & f) ^ ((~e) & g)) & 0xFFFFFFFFFFFFFFFF
            temp1 = (h + S1 + ch + k[i] + word[i]) & 0xFFFFFFFFFFFFFFFF
            S0 = (rot_right(a, 28) ^ rot_right(a, 34) ^ rot_right(a, 39)) & 0xFFFFFFFFFFFFFFFF
            maj = ((a & b) ^ (a & c) ^ (b & c)) & 0xFFFFFFFFFFFFFFFF
            temp2 = (S0 + maj) & 0xFFFFFFFFFFFFFFFF

            a1= (temp1 + temp2) & 0xFFFFFFFFFFFFFFFF
            e1 = (d + temp1) & 0xFFFFFFFFFFFFFFFF
            # Rotate the 8 variables
            a, b, c, d, e, f, g, h = a1, a, b, c, e1, e, f, g

        # adding block hashes
        hash0 = (hash0 + a) & 0xFFFFFFFFFFFFFFFF
        hash1 = (hash1 + b) & 0xFFFFFFFFFFFFFFFF
        hash2 = (hash2 + c) & 0xFFFFFFFFFFFFFFFF
        hash3 = (hash3 + d) & 0xFFFFFFFFFFFFFFFF
        hash4 = (hash4 + e) & 0xFFFFFFFFFFFFFFFF
        hash5 = (hash5 + f) & 0xFFFFFFFFFFFFFFFF
        hash6 = (hash6 + g) & 0xFFFFFFFFFFFFFFFF
        hash7 = (hash7 + h) & 0xFFFFFFFFFFFFFFFF
    #combining hash parts
    hashparts = [hash0, hash1, hash2, hash3, hash4, hash5, hash6, hash7]
    return hashparts

#|||||||||||||||||||||||||||||||||||||||||||||||||||||||#

#network connection server side
print()
print("                  ************************Listening for Connection***********************                   ")
print()
#server name and port name
host = 'local host'
port = 5004
  
#socket creation at server side
s = socket.socket(socket.AF_INET,
                  socket.SOCK_STREAM)
  
# binding socket with server and port
s.bind(('', port))
  
# listening for client connection
s.listen(1)
  
# wait for client to accept
c, addr = s.accept()
  
# display client address
print("Connected with:", str(addr))

print()
print("               **************************Recieving Hash with Message************************                ")
print()
#recieving message in encrypted cipher text


plaintext=c.recv(64)
hashcode=c.recv(1024)
plaintext=plaintext.decode()
hashcode=hashcode.decode()

print("hashcode: ", hashcode)
print()
print("Message: ", plaintext)

print()
print("               *******************************hashing Message****************************                  ")
print()
if isinstance(plaintext, str):
    plaintext = bytes(plaintext, encoding='utf8')
hashparts=sha512(plaintext)
digest = sum(shift_left(x, 64 * i) for i, x in enumerate(hashparts[::-1]))
raw = digest.to_bytes(64, 'big')
format_str = '{:0' + str(2 * 64) + 'x}'
hashcode2=format_str.format(int.from_bytes(raw, 'big'))
print("hash code of recieved message: ",hashcode2)
print()
if(hashcode2==hashcode):
        print("Message Authenticated!!!")
print()
print("#||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||#")
print()
# disconnect the server
c.close()
