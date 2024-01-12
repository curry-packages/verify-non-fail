-- Defined in Prelude:
--minBound :: Char
--minBound = chr 0

maxBound :: Char
maxBound = chr 0x10FFFF

succChar :: Char -> Char
succChar c | c < maxBound = chr $ ord c + 1

bc = succChar (minBound :: Char)

