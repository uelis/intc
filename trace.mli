(** Simplification of SSA programs by tracing. *)

(** Traces an SSA program.
    See the PPDP14 paper for an outline of the implemented
    approach. *)
val trace: Ssa.t -> Ssa.t

(** Try to avoid sequences of jumps where one could jump to
    the final label directly. *)
val shortcut_jumps: Ssa.t -> Ssa.t
