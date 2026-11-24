import YM.Integration.WilsonReportCompactFineSmear
import YM.RG17.Gathers

/-! The genuine regulated RG17 packMark with its absolute translated test,
its real atRef columns and the original independent exterior insertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportRegulatedSmear
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open Table OPE.Orbits RG12 RG17
open Next.UVStress SharpGram Extra.Histories
open WilsonReportFineSmear
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} {F : Spec.Final C f S}
variable {W r D} {n k N p : ℕ}

/-- The full absolute external test used by RG17 has the required translated
compact root support, including the degenerate or forbidden packing branch. -/
theorem shape (X : RG17.External C S) {K : Set (Points n)} (hK : IsCompact K) (ψ : Test n)
    (support : tsupport ψ⊆K) {s : ℝ} (hs : s≠0) :
    WilsonReportCompactFineSmear.supported C (N:=N) (p:=p) K s (RG17.shape X s ψ) := by
  intro y hy
  by_cases h : RG17.packs X s ψ
  · have hval : (RG17.absolute X s ψ) (Order.cells C N p y)≠0 := by simpa only [RG17.shaped X hs h] using hy
    obtain ⟨⟨z,w⟩,⟨hz,_⟩,equal⟩ := RG17.absolute_lands X hK support hs (subset_tsupport _ hval)
    refine ⟨z,hz,(RG17.openRoot.symm w).1,?_⟩
    intro j
    have coord := congrArg (fun U : Points (n+X.n) => U (Fin.castAdd X.n j)) equal
    change C.S.place (y (Fin.castAdd X.n j))=s•z j+(RG17.openRoot.symm w).1
    simpa only [RG17.absCord,RG17.pad_xy,points,WithLp.ofLp_toLp,Fin.append_left,PiLp.add_apply,
      PiLp.smul_apply,RG17.echo_at,Order.cells] using coord.symm
  · exfalso
    apply hy
    rw [RG17.shape,dif_neg (fun h' => h h'.2)]
    rfl

/-- Native regulated references, including the physical engineering scale,
pay precisely their true shifted frame mass at the layout's own level. -/
theorem reference (loc : Layout F) (s : ℝ) (q : ℕ) (u : C.label q)
    (past : C.ref q≤loc.level s) (visible : loc.level s≤N) :
    Spindle.paid C q (loc.level s) N p (RG17.atRef loc q s (N,p) u)=
      mass C q (loc.shift q s u) := by
  let m := loc.level s
  let A := C.S.a m
  have pos : 0<A := C.S.a_pos m
  let Y := RG17.atRef loc q s (N,p) u
  have charge : quota C q m N p Y=A^q*mass C q (loc.shift q s u) := by
    unfold Y RG17.atRef
    rw [quota_smul,quota_atK C F.room.cutoff _ _ (N,p) past visible,Complex.norm_real,Real.norm_of_nonneg (pow_pos pos _).le]
    · exact F.room.cutoff
    · exact past
    exact visible
  have cost : Spindle.paid C q m N p Y=(A^q)⁻¹*quota C q m N p Y := by
    unfold Spindle.paid Price.awake
    rw [Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg pos.le]
    rfl
  change Spindle.paid C q m N p Y=_
  rw [cost,charge]
  field_simp

/-- The actual sampled RG17 packMark, not an alternative coordinate evaluation.
The signed offset and charged-sector integrals refer to the very same finest
gauge field as every refTag in the original external table. -/
theorem purchased (hG : G.Simple) (book : Log.OnBudget C.path.levels) (citizen : Citizen C W r D)
    (loc : Layout F) (d : Fin n→ℕ) (t : ℕ) {K : Set (Points n)} (hK : IsCompact K)
    (hc : K⊆conf n) (B : ℕ) (big : 17≤B) :
    ∀ᶠ k : ℕ in atTop,∀ s : ℝ,0<s → s≤1 → Real.log (C.path.levels.clock.hatBeta k)^B ≤ s/C.S.a k →
    ∀ᶠ p : ℕ in atTop,∀ N : ℕ,∀ hk : k<N,∀ v : (j:Fin n)→C.label (d j),
    let Y := fun j => RG17.atRef loc (d j) s (N,p) (v j)
    (∀ j,Spindle.paid C (d j) k N p (Y j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ (X : RG17.External C S) (ψ : Test n),tsupport ψ⊆K →
    let op := RG17.shape X s ψ
    ‖RG17.packMark loc X d v s ψ (N,p)-
      ∑ y : Sites C N p n X.n,weight C op y*(sampled hk.le d Y (RG17.refTags X) y+
        offset hk.le d Y (RG17.refTags X) y+early hk.le d Y (RG17.refTags X) y)‖ ≤
    ∑ y : Sites C N p n X.n, ‖weight C op y‖*((∫ Z,‖exterior (RG17.refTags X) y Z‖ ∂law G (C.side N p) (C.beta N p))*
      Real.exp (-((C.path.levels.budget k).B:ℝ))) := by
  filter_upwards [WilsonReportCompactFineSmear.purchased hG F.room.cutoff book citizen d t hK hc B big] with k readout
  intro s hs1 hs2 window
  filter_upwards [readout s hs1 hs2 window] with p exacts N hk v
  dsimp only
  intro paid X ψ supp
  exact exacts N hk _ paid X.n (RG17.refTags X) (RG17.shape X s ψ) (shape X hK ψ supp hs1.ne')

end YM.Integration.WilsonReportRegulatedSmear
end

