import YM.LocalTaylorR2.Exponent.Grain
import YM.LocalTaylorR2.Snapshot
/-!
 # Selective expenditures at all head counts

 Not a pseudo probability invoice based on zero support or one rank. Pay
 BEFORE field projection, on the relevant common geometry. Combined-cost
 universe includes curvature of the argument probes at any rank, when
 polynomial (as needed for perturbative models).
 Adaptation E6 Shelf/Splay/Hut with a union of panic events (no cluster
 eligibility assumptions for this new bill! stores and consumed momentum unchanged).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}

abbrev buzz (i:Site c): WarningAt c f := Sum.inl (.inr (.inr (.inr (.inl i))))

def eerie (X:Coat T F)(Y:Support c)(a β:ℝ) := ⋃ i∈ (Y: Set (Site c)), X.catastrophe a β {buzz i}

lemma atHome (X:Coat T F) (Y:Support c) (a β:ℝ) (z: Air f G) (h:z∉ eerie X Y a β) : ∀ i∈Y, X.watch i a β (2*X.B) z:= by
   intro i hi j hj; by_contra hq; apply h; refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
   intro k hk; rw [mem_singleton.mp hk]; exact ⟨j,hj,(lt_of_not_ge hq).le⟩
lemma measurable_eerie (X:Coat T F) (Y:Support c)(a β:ℝ): MeasurableSet (eerie X Y a β) := MeasurableSet.iUnion fun _=> MeasurableSet.iUnion fun _=> Poll.sounded ..
lemma fracas (X:Coat T F) (Y:Support c)(a β:ℝ) (h : ∀ (i:WarningAt c f), X.dice.real (X.catastrophe a β {i}) ≤ g):
   X.dice.real (eerie X Y a β) ≤ Y.card*g:= by
   let f i:= X.dice.real (X.catastrophe a β {buzz i}); calc
     _ ≤ ∑ i∈Y,f i:= measureReal_biUnion_finset_le ..
     _ ≤ ∑ _i∈Y,g := Finset.sum_le_sum fun i _=> h _
     _ = _:= by rw [sum_const,nsmul_eq_mul]

-- Seasonal curse. Inhomogeneous so at Grow k=0 it may cost still a
-- power in front. Numerical at typical chart = 1.
def glacial (X:Coat T F)(I: Support c) (w:Air f G) (β b t:ℝ) (k:ℕ) : ℝ :=
    if w∈eerie X I b β then t*facescale (edgesM S I X.B) w^k else 1 -- G param duplicate maybe
lemma frozenWide (X:Coat T F)(I:Support c)(w: Air f G)(ht:1≤g): 1≤glacial X I w β x g k:= by unfold glacial; split; exact one_le_mul_of_one_le_of_one_le ht (one_le_pow₀ (Flux.expenses ..).1); exact le_rfl

lemma stockpile (G:Gauge)(L:Side)(o:Target.Order G W)(j:ℕ): ∃ t n, Rate G L 0 t ∧ ∀ s c f (S:StepData c f)(T:Tube G S)(P:Teller G)(Q:YM.ConnectedActivityE6.Target G P) C μ (R:Rep G f) (H:Cash W s μ L Q o C T R)(F:Forest S.ratio)(X:Coat T F), X.x=s → X.width=o.K → X.manifest → ∀ Y: Molecule S,
  let V:=1+H.shapeW Y; let Z:=edgesM S (H.unionP Y) (radiusB s)
  (∫ x,facescale Z x^j ∂X.dice) ≤ |t s| *V^n := by
   obtain ⟨K,l,hK,h⟩:= walksW G L (payE o.eta o.gap o.ample (tubularPrice G L)) j
   refine ⟨K,l,hK,?_⟩; intro s c f S T P Q C μ R H F X hv he hX Y V Z
   have hS:= H.laws.data
   have hr := globes Z (hS.localP F X hv he hX).sails j
   have hZ : (Z.card:ℝ) ≤ V*(ballCost (radiusB s))*(Itinerary.density L:ℝ) := by
     have hp:= crewsC H Y; rw [hS.funds.length_eq] at hp; apply hp.trans; gcongr; unfold V; linarith
   exact hr.2.trans (h _ _ _ V (le_add_of_nonneg_right (H.positive_volume Y)) (Nat.cast_nonneg _) hZ (by simp [lensS]))
structure Bank (H:Cash W s μ L Q o C T R)(j k n:ℕ)(x:ℝ)(m p:ℕ)(b:ℝ) : Prop where
  grant : ∀ (F:Forest S.ratio)(X:Coat T F), X.x=s → X.width=o.K → X.manifest → ∀ Y:Molecule S,
    let Z:=H.unionP Y; let U:=edgesM S Z (radiusB s); let W (y:Air f G):= glacial X Z y R.beta (o.ξ/2) b p ^ m * facescale U y^(k*j)
    Integrable W X.dice ∧ (∫ y,W y ∂ X.dice) ≤ x*(1+H.shapeW Y)^n
include H
omit H in
lemma segregate (b:ℝ)(p k:ℕ)(a:ℝ)(X:Coat T F)(U:Support c) (hr:Rotator P L g x y s X) :
    Integrable (fun w=> glacial X U w β a b p ^ m * facescale (edgesM S U X.B) w^k) X.dice := by
 let V:=eerie X U a β; let Z:=edgesM S U X.B
 let f (w:Air f G):= b^m * facescale Z w^(p*m+k); let y(w:Air _ G):= facescale Z w^k
 have he : Integrable (V.piecewise f y) X.dice := Integrable.piecewise (measurable_eerie X U a _) ((globes Z hr (p*m+k)).1.const_mul (b^m)).restrict (globes Z hr k).1.restrict
 refine he.congr (ae_of_all _ fun w=>?_)
 change V.piecewise f y w = _ ; by_cases hw: w∈eerie X U a β <;> simp [V,f,y,Z,hw,glacial,mul_pow,pow_add,pow_mul, Set.piecewise,mul_assoc]
lemma Bank.raise {b0:ℝ} (h:Bank H j k n x m p b0) -- auto implicit b0 FALSE
    (hn: n≤l)(hv: x≤y)(hx:0≤x): Bank H j k l y m p b0:= by
   refine ⟨?_⟩; intro F X hv' hK hX Y Z U D; have hh:= h.grant F X hv' hK hX Y
   have hz : 1≤1+H.shapeW Y:= le_add_of_nonneg_right (H.positive_volume _)
   exact ⟨hh.1,hh.2.trans (by gcongr; linarith)⟩
end YM.LocalTaylorR2.Exponent
