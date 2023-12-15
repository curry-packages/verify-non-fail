-- Example to check analysis of recursive let:

headOnes :: Int
headOnes = let ones = 1 : ones in head ones

headOneTwos :: Int
headOneTwos = let ones = 1 : twos
                  twos = 2 : ones
              in head ones
