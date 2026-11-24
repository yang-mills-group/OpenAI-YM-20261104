import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Lips
/-! # Comparing with the grid poses. Need uniform on those charged to C5 in s homes.
 No estimate by pointwise derivative at just one coupled shape. Keep true Near & Far
 through entire segment; Jacobian conventions when pairing see M.2 theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open FVA2.Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point Metric
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ} {I:Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {P:Set (Points n)}{E:Set (Points m)}
    {W c δ a b ε α β:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W c δ A B)
-- `cthickening` geometry. Use *positive* distances per compact.
def Amplifies (A P:Set (Points n)) : Prop := ∃ ε>0, cthickening ε A⊆P
lemma includes (h:Amplifies P A) : P⊆A := by obtain ⟨k,hk,H⟩:=h; exact (self_subset_cthickening _).trans H
lemma external : IsOpen (Outside m) := (conf_open _).preimage (O.Enh.continual continuous_const continuous_id)
lemma afford (hx:IsCompact P)(hu:P⊆conf n)(hy:IsCompact E)(hw:E⊆Outside m): ∃ A B,
    Amplifies P A ∧ Amplifies E B ∧ ∀ᶠ W in atTop,∃ c δ,Room W c δ A B := by
  obtain ⟨k,hk,h⟩ := hx.exists_cthickening_subset_open (conf_open _) hu
  obtain ⟨j,hj,p⟩:= hy.exists_cthickening_subset_open external hw
  obtain ⟨c,δ,x⟩:= arrange (hx.cthickening) h hy.cthickening p
  exact ⟨ _,_,⟨k,hk,subset_rfl⟩,⟨j,hj,subset_rfl⟩,x.mono fun i hi=>⟨c,δ,hi⟩⟩
lemma inside (h:Amplifies P A){x x':I→ Points n}(he:∀ᶠ i in F,x i∈ P)
    (hx:Tendsto (fun i=> x' i-x i) F (𝓝 0)) : ∀ᶠ i in F, segment ℝ (x i) (x' i) ⊆ A := by
  obtain ⟨k,hk,v⟩:= h; filter_upwards [he,hx.norm.eventually_lt_const (by simpa : (‖(0:Points n)‖<k))] with i h hx
  exact fun y hy=> v (mem_cthickening_of_dist_le y (x i) k P h ((dist_eq_norm ..).trans_le ((norm_sub_le_of_mem_segment hy).trans hx.le)))
def stitch (n m:ℕ): Points n × Points m →L[ℝ] Points (n+m) := by
  refine { toFun := fun i=>forest i.1 i.2, map_add' := ?_, map_smul' := ?_, cont := O.Enh.continual continuous_fst continuous_snd }
  · intro u v; ext1 i; induction i using Fin.addCases <;> simp
  intro c u; ext1 i; induction i using Fin.addCases <;> simp
lemma line_stitch (a b:Points n)(x y:Points m)(s T:ℝ): AffineMap.lineMap (joins a x T) (joins b y T) s =
    joins (AffineMap.lineMap a b s) (AffineMap.lineMap x y s) T := by
  rw [AffineMap.lineMap_apply_module,AffineMap.lineMap_apply_module,AffineMap.lineMap_apply_module]
  ext1 i; induction i using Fin.addCases <;> simp [joins,smul_add,smul_comm T]

variable {x':I→Points n}{y':I→Points m}{w:I→ℝ}
lemma cost_space (h:(fun i=> x' i-x i)=O[F] w)(hp:(fun i=>T i • (y' i-y i))=O[F] w) :
    (fun i=> joins (x' i) (y' i) (T i)-joins (x i) (y i) (T i))=O[F] w := by
  apply (((stitch n m).isBigO_comp ..).trans (h.prod_left hp)).congr_left; intro i
  rw [smul_sub]; change stitch n m ((x' i,T i • y' i)-(x i,T i • y i))=_; rw [map_sub]; rfl
lemma grow (hT:∀ᶠ i in F,1≤T i)(hp:(fun i=>T i • (y' i-y i))=O[F] w) : (fun i=>y' i -y i)=O[F] w := by
  apply (IsBigO.of_bound' ?_).trans hp; filter_upwards [hT] with i hi
  rw [ norm_smul ]; exact le_mul_of_one_le_left (norm_nonneg _) (hi.trans (le_abs_self _))

local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}
lemma closer {p:ℕ}(ht:Tendsto r F late)(hx:(fun i=>x' i-x i)=O[F] (fun i=>g0 G (r i)^(p+1)))(h:G.Simple) :
    Tendsto (fun i=> x' i-x i) F (𝓝 0) := hx.trans_tendsto (by simpa [Function.comp_def] using ((g0_zero h).pow (p+1)).comp ht)

variable {N : WilsonPrescription G} (ν:ℝ) {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S) (Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (H0:LogTrace U Q.port)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial) {A0:∀d:ℕ,ℝ→Change G d}(Z:Realized J Y N A0 (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)(hJ: Leading U J)(hp: normal U J N.store)
    (h:Aim F G W a b r T)(hb:0<b)(hx:∀ᶠ i in F,x i∈P)(hy:∀ᶠ i in F,y i∈E)
    (u: Tags G d (n+m)) (v: I→ Viewers U)
local notation "ζ" => (fun i:I=> joins (x i) (y i) (T i))
local notation "ζ'" x:max "," y:max => (fun i:I=> joins (x i) (y i) (T i))
local notation "g" => g0 G
include hx hy h hb R Z S0 H0 hp hJ H ν S1 Q U v
lemma crossing (hi : Amplifies P A)(hj:Amplifies E B)(p:ℕ) : ∀ᶠ k:ℕ in atTop, ∀ x' : I→Points n, ∀ y' : I→Points m,
    (fun i=>x' i-x i)=O[F] (fun i=>g (r i)^(k+1)) → (fun i=> T i • (y' i-y i))=O[F] (fun i=>g (r i)^(k+1)) →
      let f i:= differ (N:=N) U J Y (r i) p (v i) u; (fun i=> f i (ζ i)-f i (joins (x' i) (y' i) (T i)))=O[F] fun i=> g (r i)^(p+1) := by
  obtain ⟨K,c₀,e,H'⟩:= cost_y R ν U J Y Q H0 H Z S0 S1 hJ hp hb (a:=a) u p
  filter_upwards [eventually_ge_atTop (p+K)] with k hc x' y' hg hψ f
  let z:= (fun i:I=> joins (x' i) (y' i) (T i)); let L i:= c₀ * (g (r i))⁻¹^K
  have hd:(fun i=> z i-ζ i)=O[F] fun i=>g (r i)^(p+K+1):= (cost_space hg hψ).trans ((Fare.over_pow (p+K+1) (k+1) (by omega) late g ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))).comp_tendsto h.reach)
  apply (IsBigO.of_bound' ?_).trans (((isBigO_refl (fun i=>L i) F).mul (isBigO_norm_left.mpr hd)).trans ?_)
  · filter_upwards [ inside hi hx (closer h.reach hg sim), inside hj hy (closer h.reach (grow (aspirant R h) hψ) sim), h.reach.eventually H', h.reach.eventually self_mem_nhdsWithin,h.bud,h.high,h.reach.eventually (g0_pos sim)] with i G K' D hr w ht v
    let E:= segment ℝ (ζ i) (z i); have he(y:Points (n+m))(hy:y∈ E) : y∈conf (n+m) ∧ ‖fderiv ℝ (f i) y‖ ≤ L i := by
      unfold E z at hy; change _∈ segment ℝ _ _ at hy; rw [ segment_eq_image_lineMap ] at hy; obtain ⟨s,hs,rfl⟩:= hy; rw [line_stitch]
      let x:= G (lineMap_mem_segment ℝ _ _ hs); let y:= K' (lineMap_mem_segment ℝ _ _ hs)
      exact ⟨ R.event _ ht _ x _ y,D _ ht w _ x _ y _ ⟩
    rw [ Real.norm_of_nonneg (by unfold L; positivity : 0 ≤ L i * ‖z i - ζ i‖), norm_sub_rev]; refine (convex_segment _ _).norm_image_sub_le_of_norm_fderiv_le ?_ (fun y hy=> (he y hy).2) (left_mem_segment ..) (right_mem_segment ..); intro x hx; exact diff_smooth U J Y H hr p u _ (he x hx).1
  refine ((isBigO_refl _ _).const_mul_left c₀).congr' ?_ (EventuallyEq.refl ..); filter_upwards [h.reach.eventually (g0_pos sim)] with i h; unfold L; rw [ show p+K+1=K+(p+1) by omega, pow_add _ K (p+1), inv_pow,mul_assoc, ← mul_assoc _ _ (_^(p+1)), inv_mul_cancel₀ (pow_ne_zero _ h.ne'),one_mul ]
end YM.FVA2.GradedFar259.Flash
