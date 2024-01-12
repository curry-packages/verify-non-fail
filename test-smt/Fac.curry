fac :: Int -> Int
fac n | n == 0 = 1
      | n > 0  = n * fac (n - 1)

--fac'nonfail :: Int -> Bool
--fac'nonfail n = n >= 0

{-
FlatCurry representation:

fac :: Int -> Int
fac v1 = case (v1 _impl#==#Prelude.Eq#Prelude.Int 0) of
     True -> 1
     False -> case (((_impl#>#Prelude.Ord#Prelude.Int) v1) 0) of
       True -> v1 _impl#*#Prelude.Num#Prelude.Int (fac (v1 _impl#-#Prelude.Num#Prelude.Int 1))
       False -> failed
    
fac :: Int -> Int
fac v1 = case (v1 == 0) of
     True -> 1
     False -> case (v1 > 0) of
       True -> v1 * (fac (v1 - 1))
       False -> failed (*)

Collect information about non-variable cases at (*):

(v1 == 0) = False /\ (v1 > 0) = False

Since "False" is the non-fail condition of failed, a successful proof
should ensure

((v1 == 0) = False /\ (v1 > 0) = False) => False

This is equivalent to

not ((v1 == 0) = False /\ (v1 > 0) = False) \/ False

or

(v1 == 0) = True \/ (v1 > 0) = True

Add this as a non-fail condition to fac and verify again.
Now we have to (*) the following collected information:

((v1 == 0) = True \/ (v1 > 0) = True) /\ (v1 == 0) = False /\ (v1 > 0) = False

This is SMT equivalent to

v1 >= 0 /\ v1 /= 0 /\ v1 <= 0

and, thus, unsatisfiable. Hence, the branch is unreachable.
Furthermore, the precondition at the recursive call to fac is

((v1 == 0) = False /\ (v1 > 0) = True)

This implies

(v1 - 1) >= 0

so that the non-fail conditions holds.


Description of the inference method:
------------------------------------

Operations have call types as well as call conditions (Boolean expressions
over the arguments). The latter are initially `True`.

1. Collect non-type representable information in addition to abstract type.
   In particular, if the case discriminator is not a variable.

2. If some non-fail condition does not hold, add it to the current
   non-fail condition (only if arguments are involved?).

3. Try the proof again.


Call conditions for predefined predicates:

div, mod,...: v2 /= 0

Advantages:

- Improve code by not checking unreachabel branches, i.e., translate

      fac n | n == 0 = 1
            | n > 0  = n * fac (n - 1)
      
  (after verification) into
      
      fac n | n == 0    = 1
            | otherwise = n * fac (n - 1)

-}

  

