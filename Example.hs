{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Example where

import qualified Prelude


#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

data Stream a =
   Scons a (Stream a)

forever :: a1 -> Stream a1
forever x =
  Scons x (forever x)

data Zipper a =
   Zip (Stream a) a (Stream a)

left :: (Zipper a1) -> Stream a1
left z =
  case z of {
   Zip left0 focus0 right0 -> left0}

focus :: (Zipper a1) -> a1
focus z =
  case z of {
   Zip left0 focus0 right0 -> focus0}

right :: (Zipper a1) -> Stream a1
right z =
  case z of {
   Zip left0 focus0 right0 -> right0}

moveLeft :: (Zipper a1) -> Zipper a1
moveLeft z =
  case z of {
   Zip left0 c rs ->
    case left0 of {
     Scons l ls -> Zip ls l (Scons c rs)}}

moveRight :: (Zipper a1) -> Zipper a1
moveRight z =
  case z of {
   Zip ls c right0 ->
    case right0 of {
     Scons r rs -> Zip (Scons c ls) r rs}}

setFocus :: a1 -> (Zipper a1) -> Zipper a1
setFocus x z =
  case z of {
   Zip ls focus0 rs -> Zip ls x rs}

modFocus :: (a1 -> a1) -> (Zipper a1) -> Zipper a1
modFocus f z =
  case z of {
   Zip ls x rs -> Zip ls (f x) rs}

data Instructions =
   Read
 | Write
 | Inc
 | Dec
 | L
 | R

instructions_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Instructions -> a1
instructions_rect f f0 f1 f2 f3 f4 i =
  case i of {
   Read -> f;
   Write -> f0;
   Inc -> f1;
   Dec -> f2;
   L -> f3;
   R -> f4}

instructions_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Instructions -> a1
instructions_rec =
  instructions_rect

type Commands = Instructions

type Response = ()

data EffectTree a =
   Pure a
 | Eff Commands (Response -> EffectTree a)

type Tape = Zipper Prelude.Integer

type Prog = ([]) Commands

eval :: (EffectTree a1) -> Tape -> Prelude.IO a1
eval mx t =
  let {tapeMod = \f cont -> Prelude.id (eval (cont ()) (f t))} in
  case mx of {
   Pure x -> Prelude.return x;
   Eff c cont ->
    case c of {
     Read -> (Prelude.>>=)
      (Prelude.fmap (Prelude.toInteger Prelude.. Prelude.fromEnum) Prelude.getChar)
      (\x -> eval (cont ()) (setFocus (unsafeCoerce x) t));
     Write -> (Prelude.>>=)
      ((Prelude.putChar Prelude.. Prelude.toEnum Prelude.. Prelude.fromInteger)
      (focus t)) (\x -> eval (cont ()) t);
     Inc -> tapeMod (modFocus (\x -> (Prelude.+) x (Prelude.succ 0))) cont;
     Dec -> tapeMod (modFocus (\x -> (Prelude.-) x (Prelude.succ 0))) cont;
     L -> tapeMod moveLeft cont;
     R -> tapeMod moveRight cont}}

compile :: Prog -> EffectTree ()
compile p =
  case p of {
   [] -> Pure ();
   (:) x xs -> Eff x (\x0 -> compile xs)}

yell :: ([]) Instructions
yell =
  (:) Read ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec
    ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec
    ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec
    ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec ((:) Dec
    ((:) Dec ((:) Write ((:) R ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc
    ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc
    ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc
    ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc ((:) Inc
    ((:) Inc ((:) Inc ((:) Inc ((:) Write
    yell)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

zeroes :: Stream Prelude.Integer
zeroes =
  forever 0

emptyTape :: Zipper Prelude.Integer
emptyTape =
  Zip zeroes 0 zeroes

main :: Prelude.IO ()
main =
  eval (compile yell) emptyTape

