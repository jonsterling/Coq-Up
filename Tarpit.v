Require Import ZArith List.
Require Import Basics.

Set Implicit Arguments.
Open Scope nat_scope.

Module Tarpit. 
  Section DataTypes.
    Variable A : Type.
    CoInductive stream  : Type :=
    | SCons : A -> stream -> stream.

    CoFixpoint forever (x : A) : stream := SCons x (forever x).
    
    Record zipper := Zip
                      { left  : stream ;
                        focus : A ;
                        right : stream
                      }.

    Definition moveLeft (z : zipper) : zipper :=
      match z with
        | Zip (SCons l ls) c rs => Zip ls l (SCons c rs)
      end.
    
    Definition moveRight (z : zipper) : zipper :=
      match z with
        | Zip ls c (SCons r rs) => Zip (SCons c ls) r rs
      end.

    Definition setFocus (x : A) (z : zipper) :=
      match z with
        | Zip ls _ rs => Zip ls x rs
      end.

    Definition modFocus (f : A -> A) (z : zipper) :=
      match z with
        | Zip ls x rs => Zip ls (f x) rs
      end.

  End DataTypes.

  Definition tape := zipper nat.

  Section IO.

    Inductive Free {C : Type} {R : C -> Type} (A : Type) : Type :=
    | pure : A -> Free A
    | eff  : forall (c : C) (p : R c -> Free A), Free A.
    
    Inductive IOC :=
    | Write : IOC
    | Plus : nat -> IOC
    | Read : IOC
    | L : IOC
    | R : IOC.

    Definition FIO := @Free IOC (fun _ => unit).
  End IO.

  Section Haskell.
    Parameter HS_IO : Type -> Type.
    Parameter HS_return : forall (A : Type) (a : A), HS_IO A.
    Parameter HS_bind : forall (A B : Type) (a : HS_IO A) (f : A -> HS_IO B), HS_IO B.
    Parameter HS_write : nat -> HS_IO unit.
    Parameter HS_read : HS_IO nat.
  End Haskell.


  Section Compiler.
    Definition prog := list IOC.
    Fixpoint eval {A} (mx : FIO A) (t : tape) : HS_IO A :=
      let tapeMod := fun f cont => eval (cont tt) (f t) in
      match mx with
        | pure x => HS_return x
        | eff Write cont => HS_bind (HS_write (focus t)) (fun _ => eval (cont tt) t)
        | eff Read cont => HS_bind HS_read (fun x => eval (cont tt) (setFocus x t))
        | eff L cont => tapeMod (@moveLeft _) cont
        | eff R cont => tapeMod (@moveRight _) cont
        | eff (Plus n) cont => tapeMod (modFocus (fun x => n + x)) cont
      end.

    Fixpoint compile (p : prog) : FIO _ :=
      match p with
        | nil => pure tt
        | x :: xs => eff x (fun _ => compile xs)
      end.
  End Compiler.
End Tarpit.

Module Examples.
  Import Tarpit.

  Notation " y ;; b " := (HS_bind y (fun _ => b)) (right associativity, at level 60).

  Definition testProgram : prog :=
    (Read :: Write :: Plus 4 :: Write :: nil).
  
  Definition zeroes : stream nat := forever 0.
  Definition main := eval (compile testProgram) (Zip zeroes 1 zeroes).
End Examples.

Import Tarpit.
Extract Constant HS_IO "a" => "IO".
Extract Inlined Constant HS_return  => "return".
Extract Inlined Constant HS_bind => "(>>=)".
Extract Inlined Constant HS_write => "print".
Extract Inlined Constant HS_read => "((fmap read getLine) :: IO Integer)".
Extract Inductive nat => "Integer" ["0" "succ"]
  "(\fO fS n -> if n==0 then fO () else fS (n-1))".
Extract Inlined Constant plus => "(+)".
Extract Inlined Constant mult => "(*)".
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive unit => "()" [ "()" ].

Extraction Inline HS_IO. 

Extraction Language Haskell.
Extraction "Example" Examples.