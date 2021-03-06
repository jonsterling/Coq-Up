Require Import List.

Set Implicit Arguments.

Module Language.
  Section DataTypes.
    Variable A : Type.

    CoInductive stream :=
    | scons : A -> stream -> stream.

    CoFixpoint forever x := scons x (forever x).

    CoInductive colist :=
    | conil  : colist
    | cocons : A -> colist -> colist.

    Record zipper := Zip
      { left  : stream ;
        focus : A ;
        right : stream
      }.

    Definition moveLeft z :=
      match z with
        | Zip (scons l ls) c rs => Zip ls l (scons c rs)
      end.

    Definition moveRight z :=
      match z with
        | Zip ls c (scons r rs) => Zip (scons c ls) r rs
      end.

    Definition setFocus x z :=
      match z with
        | Zip ls _ rs => Zip ls x rs
      end.

    Definition modFocus f z :=
      match z with
        | Zip ls x rs => Zip ls (f x) rs
      end.

  End DataTypes.

  Module Type CommandResponse.
    Parameter commands : Set.
    Parameter response : commands -> Type.
  End CommandResponse.

  Module EffectTree (Import cr : CommandResponse).
    CoInductive EffectTree A :=
    | pure : A -> EffectTree A
    | eff  : forall c, (response c -> EffectTree A) -> EffectTree A.
    Implicit Arguments eff [A].
    Export cr.
  End EffectTree.

  CoInductive HS_IO : Type -> Type :=
  | HS_return : forall A, A -> HS_IO A
  | HS_bind : forall A B, HS_IO A -> (A -> HS_IO B) -> HS_IO B
  | HS_write : nat -> HS_IO unit
  | HS_read : HS_IO nat
  | HS_id : forall A, HS_IO A -> HS_IO A.

  Module IO <: CommandResponse.
    Inductive instructions := Read | Write | Inc | Dec | L | R.
    Definition commands := instructions.
    Definition response (c : commands) := unit.
  End IO.

  Module IOTree := EffectTree IO.
  Section Program.
    Import IOTree.

    Definition tape := zipper nat.
    Definition prog := colist commands.

    CoFixpoint eval {A} (mx : EffectTree A) (t : tape) : HS_IO A :=
      let tapeMod := fun f cont => HS_id (eval (cont tt) (f t)) in
      match mx with
        | pure x => HS_return x
        | eff c cont =>
          match c with
            | Write => HS_bind (HS_write (focus t)) (fun _ => eval (cont tt) t)
            | Read => HS_bind HS_read (fun x => eval (cont tt) (setFocus x t))
            | L => tapeMod (@moveLeft _) cont
            | R => tapeMod (@moveRight _) cont
            | Inc => tapeMod (modFocus (fun x => x + 1)) cont
            | Dec => tapeMod (modFocus (fun x => x - 1)) cont
          end
      end.

    CoFixpoint compile (p : prog) : EffectTree _ :=
      match p with
        | conil => pure tt
        | cocons x xs => eff x (fun _ => compile xs)
      end.
  End Program.

  Export IOTree.
End Language.

Module Notations.
  Import Language.

  Infix " ::: " := cocons (right associativity, at level 100).

  (* A terminating program is a list of semicolon-separated
     instructions in [| ... |]. *)

  Notation "[| x ; .. ; y |]" := (x ::: .. (y ::: (conil _)) ..)
                                  (at level 100).


  (* [| a ; b ; c |> r concatenates the program in the brackets with
     the program [r]; this can be used for making coinductive
     programs, such as REPLs. *)

  Notation "[[| x ; .. ; y |> r" := (x ::: .. (y ::: r) ..)
                                     (at level 100).

  (* If readable code isn't your speed, we can also use some Brainfuck
  inspired notation. *)

  Notation "> x" := (R ::: x) (at level 100).
  Notation "< x" := (L ::: x) (at level 100).
  Notation "++ x" := (Inc ::: x) (at level 100).
  Notation "-- x" := (Dec ::: x) (at level 100).
  Notation "! x" := (Write ::: x) (at level 100).
  Notation "# x" := (Read ::: x) (at level 100).
  Notation "$" := (conil _).

End Notations.

Module Examples.
  Import Language.
  Import Notations.

  (* This little program will capitalize every letter you type! But
  when it tries to capitalize non-letters, weird things will happen!
  For instance, period ends up activating the special SO key, which
  swaps in a bizarre character set; slash does the opposite. *)

  CoFixpoint yell :=
    #----------------------------------------------------------------!>
    ++++++++++++++++++++ ++++++++++++++++++++ ++++++++++++++++++++++++ ! yell.

  Definition zeroes := forever 0.
  Definition emptyTape := Zip zeroes 0 zeroes.
  Definition main := eval (compile yell) emptyTape.
End Examples.

Module Extractions.
  Import Language.
  Extraction Language Haskell.

  Extract Inductive HS_IO => "Prelude.IO"
                              [ "Prelude.return"
                                "(Prelude.>>=)"
                                "(Prelude.putChar Prelude.. Prelude.toEnum Prelude.. Prelude.fromInteger)"
                                "(Prelude.fmap (Prelude.toInteger Prelude.. Prelude.fromEnum) Prelude.getChar)"
                                "Prelude.id" ].
  Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
    "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
  Extract Inlined Constant plus => "(Prelude.+)".
  Extract Inlined Constant minus => "(Prelude.-)".
  Extract Inlined Constant mult => "(Prelude.*)".
  Extract Inductive colist => "([])" [ "[]" "(:)" ].
  Extract Inductive list => "([])" [ "[]" "(:)" ].
  Extract Inductive unit => "()" [ "()" ].
End Extractions.

Extraction "Example" Examples.
