import YangMills.WilsonProof.NativeSupport.FrozenRosterInput

/-! The signed thermal comparison for the frozen consumer's exact
one-slot difference and the actual remaining factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster
open scoped Classical BigOperators Topology
variable {G : Gauge}

def grades (a : Roster G) (s : Finset (Fin a.length)) (j : ↥s) :=
  (a.get j.val).1

def labels (a : Roster G) (s : Finset (Fin a.length)) (j : ↥s) :
    ((frames G).level (grades a s j)).Index := (a.get j.val).2

theorem actual_planted (R : Run G) {u per : ℕ} (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length → Site (R.family.side (u+1) per)) (i : Fin a.length) (hi : i∈s)
    (z e : Site (R.family.side (u+1) per)) (b : Bool) :
    WilsonReportFrozenTraversal.planted R a s o i z e b = fun U =>
      wordAt (grades a s) (labels a s) (fun j=>Function.update o i z j.val) b U -
      wordAt (grades a s) (labels a s) (fun j=>Function.update o i e j.val) b U := by
  funext U
  unfold WilsonReportFrozenTraversal.planted
  rw [←WilsonOffsetJointRoster.paired a s i hi o z e U,map_sub]
  rfl

theorem planted_thermal (R : Run G) (simple : G.Simple)
    (slow : ∀ j, ((R.alloy.B.a.budget j).supportExponent+1)*
      (((R.alloy.B.a.S.block (j-1)).val:ℝ)^4) ≤ Real.sqrt (R.alloy.B.a.clock.hatBeta j))
    (a : Roster G) (s : Finset (Fin a.length)) (s₀ W Q : ℕ)
    (stencils : ∀ j : ↥s,minSide G (grades a s j) ≤ s₀) (wanted : 1≤Q) :
    ∀ᶠ k:ℕ in atTop, ∀ u t, k≤t → ∀ ht:t<u+1,
      ((u+1-t:ℕ):ℝ)*Real.log 3 ≤ R.family.S.scale (u+1)-R.family.S.scale t →
      R.family.S.scale (u+1)-R.family.S.scale t ≤ (W:ℝ)*Real.log (R.alloy.B.a.clock.hatBeta (u+1)) →
      ∀ per, ∀ T : Slices R.family.path.levels per,
      ∀ o : Fin a.length → Site (R.family.side (u+1) per), ∀ i : Fin a.length, i∈s →
      ∀ z e : Site (R.family.side (u+1) per), ∀ b : Bool, ∀ p, 2*halfOrder W Q≤p → ∀ v : ℕ→ℝ,
        let d:=traversal T ht.le
        let B:=RGComparison.Core16.line R.family.path per t (u+1)
        let Y:=WilsonUniformUnmarkedInletSignedResponse.line B v 1
        let g:=regulatorRun R.family (u+1) per (u+1)
        let Z:=WilsonReportFrozenTraversal.planted R a s o i z e b
        v d.depth=0 → (∀ j,0<j → j<d.depth → |v j| ≤ g^p) →
        |d.conditioned Y Z 1-d.conditioned B Z 1| ≤
          6*2^(s.card+Q)*bill (grades a s) G*g^(2*Q) := by
  filter_upwards [original_thermal R simple slow (grades a s) (labels a s) s₀ W Q stencils wanted] with k ready
  intro u t kt ht steps roof per T o i hi z e b p price v d B Y g Z top band
  have receipt := ready t (u+1) kt ht steps roof per T (fun j=>Function.update o i z j.val)
    (fun j=>Function.update o i e j.val) b p price v top band
  simpa only [d,B,Y,g,Z,actual_planted R a s o i hi z e b,Fintype.card_coe,pow_add,
    mul_assoc,mul_left_comm,mul_comm] using receipt

end YM.Integration.InletSusceptibility.Packet
