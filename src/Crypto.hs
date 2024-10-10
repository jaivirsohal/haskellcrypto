module Crypto ( gcd, smallestCoPrimeOf, phi, computeCoeffs, inverse
              , modPow, genKeys, rsaEncrypt, rsaDecrypt, toInt, toChar
              , add, subtract, ecbEncrypt, ecbDecrypt
              , cbcEncrypt, cbcDecrypt ) where

import Data.Char

import Prelude hiding (gcd, subtract)

{-
The advantage of symmetric encryption schemes like AES is that they are efficient
and we can encrypt data of arbitrary size. The problem is how to share the key.
The flaw of the RSA is that it is slow and we can only encrypt data of size lower
than the RSA modulus n, usually around 1024 bits (64 bits for this exercise!).

We usually encrypt messages with a private encryption scheme like AES-256 with
a symmetric key k. The key k of fixed size 256 bits for example is then exchanged
via the aymmetric RSA.
-}

-------------------------------------------------------------------------------
-- PART 1 : asymmetric encryption

-- | Returns the greatest common divisor of its two arguments
gcd :: Int -> Int -> Int
gcd m 0 = m
gcd m n = gcd n (mod m n)

-- | Euler Totient function
phi :: Int -> Int
phi m = length [a | a <- [1..m], gcd a m == 1]

{-|
Calculates (u, v, d) the gcd (d) and Bezout coefficients (u and v)
such that au + bv = d
-}
computeCoeffs :: Int -> Int -> (Int, Int)
computeCoeffs a 0 = (1, 0)
computeCoeffs a b = 
  let (u', v') = computeCoeffs b (a `mod` b)
      q = a `div` b
  in (v', u' - q*v')
                  

-- | Inverse of a modulo m
inverse :: Int -> Int -> Int
inverse a m
  | (gcd a m == 1) && (a * u + m * v == 1) = u `mod` m
  where (u, v) = computeCoeffs a m


-- | Calculates (a^k mod m)
modPow :: Int -> Int -> Int -> Int
modPow a 0 m = 1 `mod` m
--modPow a k m = (a * modPow a (k-1) m) `mod` m
modPow a k m
    | even k = (halfPow * halfPow) `mod` m
    | otherwise = (a * modPow a (k - 1) m) `mod` m
    where halfPow = modPow a (k `div` 2) m

-- | Returns the smallest integer that is coprime with phi
smallestCoPrimeOf :: Int -> Int
smallestCoPrimeOf a = minimum [b | b <- [2..a+1], gcd a b == 1]

{-|
Generates keys pairs (public, private) = ((e, n), (d, n))
given two "large" distinct primes, p and q
-}
genKeys :: Int -> Int -> ((Int, Int), (Int, Int))
genKeys p q =
  let n = p*q
      prod = (p-1)*(q-1) -- note - is it acceptable to name this phi?
      e = smallestCoPrimeOf prod
      d = inverse e prod
  in ((e, n), (d, n))


-- | This function performs RSA encryption
rsaEncrypt :: Int        -- ^ value to encrypt
           -> (Int, Int) -- ^ public key
           -> Int
rsaEncrypt x key = modPow x e n
  where (e, n) = key

-- | This function performs RSA decryption
rsaDecrypt :: Int        -- ^ value to decrypt
           -> (Int, Int) -- ^ public key
           -> Int
rsaDecrypt x key = modPow x d n
  where (d, n) = key

-------------------------------------------------------------------------------
-- PART 2 : symmetric encryption

-- | Returns position of a letter in the alphabet
toInt :: Char -> Int
toInt a
   | a >= 'A' && a <= 'Z' = ord a - uppOffset
   | a >= 'a' && a <= 'z' = ord a - lowOffset
   where uppOffset = 65
         lowOffset = 97

-- | Returns the n^th letter
toChar :: Int -> Char
toChar n = chr (ascOffset + n `mod` 26)
   where ascOffset = 97

-- | "adds" two letters
add :: Char -> Char -> Char
add a b = toChar ((toInt a + toInt b) `mod` 26)

-- | "subtracts" two letters
subtract :: Char -> Char -> Char
subtract a b = toChar ((toInt a - toInt b) `mod` 26)

-- the next functions present
-- 2 modes of operation for block ciphers : ECB and CBC
-- based on a symmetric encryption function e/d such as "add"

-- | ecb (electronic codebook) encryption with block size of a letter
ecbEncrypt :: Char -> [Char] -> [Char]
ecbEncrypt k m = [ add x k | x <- m]

-- | ecb (electronic codebook) decryption with a block size of a letter
ecbDecrypt :: Char -> [Char] -> [Char]
ecbDecrypt k m = [ subtract x k | x <- m]

-- | cbc (cipherblock chaining) encryption with block size of a letter
cbcEncrypt :: Char   -- ^ public key
           -> Char   -- ^ initialisation vector `iv`
           -> [Char] -- ^ message `m`
           -> [Char]
cbcEncrypt _ _ [] = []
cbcEncrypt k iv (m:ms) = x : cbcEncrypt k x ms  
   where x = add (add m iv) k

-- | cbc (cipherblock chaining) decryption with block size of a letter
cbcDecrypt :: Char   -- ^ private key
           -> Char   -- ^ initialisation vector `iv`
           -> [Char] -- ^ message `m`
           -> [Char]
cbcDecrypt _ _ [] = []
cbcDecrypt k iv (c:m) = x : cbcDecrypt k c m  
   where x = subtract (subtract c k) iv 