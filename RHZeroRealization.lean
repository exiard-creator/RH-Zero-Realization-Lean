/- 
This file formalizes the logical layer of
"Zero-Inaccessible Realization and Isometric Theta-Profile Exchange".

It does not formalize the analytic construction of the completed zeta
function, the theta integral, or the proof that theta-profile exchange is
equivalent to the critical line. Those mathematical results enter through
`exchange_iff_axis` in `Spec`. No `axiom`, `sorry`, or `admit` is used.
-/

namespace AMMCL
namespace RHZeroRealization

universe u

/--
The predicates needed by the axiom-relative critical-line argument.

`exchange_iff_axis` represents the unconditional theta-profile theorem proved
in the paper: a profile pair is isometrically exchangeable exactly on the
centered critical axis.
-/
structure Spec (Point : Type u) where
  formalZero : Point → Prop
  onCriticalAxis : Point → Prop
  isometricallyExchangeable : Point → Prop
  exchange_iff_axis : ∀ point,
    isometricallyExchangeable point ↔ onCriticalAxis point

namespace Spec

variable {Point : Type u} (spec : Spec Point)

/-- The universal xi zero-realization application axiom. -/
def UniversalRealization : Prop :=
  ∀ point, spec.formalZero point → spec.isometricallyExchangeable point

/-- The centered critical-line statement. -/
def CriticalLineStatement : Prop :=
  ∀ point, spec.formalZero point → spec.onCriticalAxis point

/-- A formal zero outside the centered critical axis. -/
def OffAxisZero : Prop :=
  ∃ point, spec.formalZero point ∧ ¬ spec.onCriticalAxis point

/-- A physically realized zero is a formal zero with isometric exchange. -/
def PhysicallyRealizedZero (point : Point) : Prop :=
  spec.formalZero point ∧ spec.isometricallyExchangeable point

/--
The CRP/CRD-relative critical-line theorem: universal zero realization and
the theta-profile exchange theorem force every formal zero onto the axis.
-/
theorem criticalLine_of_universalRealization
    (realization : spec.UniversalRealization) :
    spec.CriticalLineStatement := by
  intro point zeroAtPoint
  exact (spec.exchange_iff_axis point).mp (realization point zeroAtPoint)

/-- Critical-axis membership supplies the exchange required by realization. -/
theorem universalRealization_of_criticalLine
    (criticalLine : spec.CriticalLineStatement) :
    spec.UniversalRealization := by
  intro point zeroAtPoint
  exact (spec.exchange_iff_axis point).mpr (criticalLine point zeroAtPoint)

/-- The universal realization axiom has exactly critical-line strength. -/
theorem universalRealization_iff_criticalLine :
    spec.UniversalRealization ↔ spec.CriticalLineStatement := by
  constructor
  · intro realization
    exact criticalLine_of_universalRealization spec realization
  · intro criticalLine
    exact universalRealization_of_criticalLine spec criticalLine

/-- Classification of physically realized zeros. -/
theorem physicallyRealizedZero_iff
    (point : Point) :
    spec.PhysicallyRealizedZero point ↔
      spec.formalZero point ∧ spec.onCriticalAxis point := by
  constructor
  · intro realized
    exact ⟨realized.1, (spec.exchange_iff_axis point).mp realized.2⟩
  · intro realized
    exact ⟨realized.1, (spec.exchange_iff_axis point).mpr realized.2⟩

/-- One off-axis zero directly refutes universal zero realization. -/
theorem offAxisZero_refutes_universalRealization
    (counterexample : spec.OffAxisZero) :
    ¬ spec.UniversalRealization := by
  intro realization
  obtain ⟨point, zeroAtPoint, offAxis⟩ := counterexample
  exact offAxis <|
    (spec.exchange_iff_axis point).mp (realization point zeroAtPoint)

/--
Exact falsification condition. Classical logic is used only for the converse
direction from failure of a universal implication to an existential witness.
-/
theorem not_universalRealization_iff_offAxisZero :
    ¬ spec.UniversalRealization ↔ spec.OffAxisZero := by
  classical
  constructor
  · intro realizationFails
    apply Classical.byContradiction
    intro noOffAxisZero
    apply realizationFails
    intro point zeroAtPoint
    apply (spec.exchange_iff_axis point).mpr
    apply Classical.byContradiction
    intro offAxis
    exact noOffAxisZero ⟨point, zeroAtPoint, offAxis⟩
  · intro counterexample
    exact offAxisZero_refutes_universalRealization spec counterexample

/-- The contradiction used in the paper, isolated at one formal zero. -/
theorem offAxisZero_contradiction
    (realization : spec.UniversalRealization)
    {point : Point}
    (zeroAtPoint : spec.formalZero point)
    (offAxis : ¬ spec.onCriticalAxis point) : False := by
  exact offAxis <|
    (spec.exchange_iff_axis point).mp (realization point zeroAtPoint)

end Spec
end RHZeroRealization
end AMMCL
