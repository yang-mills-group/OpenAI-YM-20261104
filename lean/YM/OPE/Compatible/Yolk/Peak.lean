import YM.OPE.Compatible.Yolk.Slush
/-!
 # On ONE activation, exact estimates. Light.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
def awash (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ x H:ℝ):ℝ:= H*tolls Q L μ x + freight Q L μ x * Real.exp (-Q.mark L μ x)
def glen (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ x H:ℝ):ℝ:= Real.exp (P.top.supportExponent-Q.ε)*(awash Q L μ x H+(Real.exp (((8*L.val+2:ℕ):ℝ)*incomingK G L x)-1)*freight Q L μ x)
structure Sparta (R:Rep G f) (S:StepData c f) (F:Tree.Forest S.ratio) (V:Config G c) (a e w b t:ℝ): Prop where
    branch:0<S.push R.beta R.eval V
    charge:Cinch R S a e V
    leaves:Besotted R S a e V w
    flare (i:F.Free) : ‖S.push R.beta (fun U:Config G f=> R.eval U * film F i U b) V‖ ≤ S.push R.beta R.eval V * t
section
variable (X:Coat T F)(H:Cash W X.x μ L Q o C T R)
local notation "t"=> (P.top.supportExponent-Q.ε)
include H in
lemma price_j (hy:Peals Q o S.patch L μ X.x s C) : 0≤freight Q L μ X.x ∧ 0≤ tolls Q L μ X.x:=by
   obtain ⟨-,hp,hq,hH,hV⟩:= hy.visible H rfl
   have ht:= hp.γ; have ht':= hq.γ; have hk:= hp.grows; have hk':=hq.grows
   have hv:0≤Q.goal L X.x:=(arable H).le
   constructor
   · change 0≤ (swing Q L μ R.beta X.x C).ceiling 0 0 0 0 / Q.goal L X.x
     apply div_nonneg _ hv; unfold Mixed.Costs.ceiling Reserves.extract Reserves.polyPrice Reserves.treeYield; positivity
   change 0≤ (arcs Q L μ R.beta X.x C).ceiling 0 0 0 0 / Q.goal L X.x
   apply div_nonneg _ hv; unfold Mixed.Costs.ceiling Reserves.extract Reserves.polyPrice Reserves.treeYield; positivity
variable (hw:X.width=o.K) (hz:Stamp T) -- edit
 {V d B a b e:ℝ}(hq:Cash.Renewed m a b e H)(hx:Peals Q o S.patch L μ X.x s C)(hu:((X.B*2+1:ℕ):ℝ)^4*(Q.overture L μ X.x m*(1-1/2)⁻¹)≤ Q.exp)
 (hm:mazur S.patch Q o L μ X.x s C d B E)(hp:foam Q L)(hE:0≤E) {g:LogField G c} (hG:X.V=represent g) (hg:‖g‖≤d)
 (he:RG.flags (Pressure.temp X.x) X.V=∅)
include H hw hm hq hx hu hz hE hG hg he hp
lemma terrain (hk:HasSlots R.p R.activities)(hb:4*S.patch.L.val+1≤R.p.B):
    Sparta R S F X.V t (freight Q L μ X.x) (incomingK G L X.x) B (glen Q L μ X.x E):=by
   let r:=swing Q L μ R.beta X.x C
   obtain ⟨hr',ht',hT⟩ := hx.visible H rfl
   obtain ⟨hL,hT,h₀⟩:= hT
   have hl := H.laws.data.funds.length_eq
   have hf:= granted X H hw he hq hu hp hr' hL
   let Z:= S.push R.beta R.eval X.V; have hv:0<Z:=by
       unfold Z; rw [← slogan X H hw he]
       have hj := bill_vars X H hw hq
       let Φ:= H.smallAt; refine mul_pos (overhead_pos X H) ( (Gas.price_log (blocked Φ) (H.entries X) ⟨fun _=> Or.inl rfl,fun _ _=>blocked_back _⟩ Φ X.B (literal_test Φ (fun i:H.ThinP=> i.property.1)) (add_nonneg hq.full hq.post.le) hj).2.2.2.1)
   obtain ⟨hs,hv'⟩:= price_j X H hx; have hm' : t=R.p.supportExponent-Q.ε := by rw [H.laws.intake.exponent]
   have h₂:t≥0:=by nlinarith [Q.grants.1,Q.usable]
   let z:= freight Q L μ X.x
   have hz' : Cinch R S t z X.V:=by rw [hm']; exact hf
   let w:=incomingK G L X.x; have hx' : R.Lawful P.top.width P.top.paths (loopBill G L X.x) (incomingE G L X.x) w := by unfold w; rw [← hl]; exact H.laws.intake.cap
   have ha' : t ≤ R.p.supportExponent:=by rw [hm']; exact sub_le_self _ Q.usable.le
   have hk':=beaming (Keeper.sufficient hk) hx' hz' (S.isKernel (funds_branch H.laws.intake.ready) _) hs hv.le h₂ ha'
   refine ⟨hv,hz',hk',fun i=>?_⟩
   let Y:= awash Q L μ X.x E
   let j:=walksAt F i.val
   have hY:∀ M:Leaf S R,(∀ y:F.Slice G,M.ingredient (F.drape y)≠0→B<G.chord (y i))→‖S.push R.beta M.cicada X.V‖ ≤ Z*(Y*Real.exp (t*coverNumber R.p.B M.crest)*M.weight):=by
      intro M h; apply (vine H rfl hz X rfl hw he hx hm hq hu hE hG hg M i h hp).trans_eq
      apply congr_arg (Z*·); rw [scalar_z, hm']; unfold Y awash tolls; rw [← conformation Q L μ R.beta X.x C,
        show (arcs Q L μ R.beta X.x C).ceiling 0 0 0 0=(arcs Q L μ 1 X.x 0).ceiling 0 0 0 0 from rfl]; ring
      exact H
   apply (overtakes (S.isKernel (funds_branch H.laws.intake.ready) _) hx' hk F i hk' hY).trans; apply mul_le_mul_of_nonneg_left _ hv.le; unfold glen; apply mul_le_mul _ _ _ (Real.exp_pos _).le
   · apply Real.exp_monotone; apply (mul_le_mul_of_nonneg_left (by exact_mod_cast coverPeal F i.val hb) h₂).trans_eq (mul_one _)
   · apply add_le_add le_rfl; apply mul_le_mul_of_nonneg_right _ hs; gcongr; exacts [Real.exp_nonneg _, by rw [←hl]; exact_mod_cast (costPose F i.val).2] -- test
   have hP:1≤ Real.exp ((j.card:ℝ)*w):=Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)); refine add_nonneg ?_ (mul_nonneg (sub_nonneg.mpr hP) hs)
   exact add_nonneg (mul_nonneg hE hv') (mul_nonneg hs (Real.exp_nonneg _))
end
end YM.PhysicalNext.Repeat.Aroma
