import YM.FVAAlt2.Shop.Lobby
/-! Quantitative regulator estimates for the actual Mark.C's formal
Wilson moments before position normalization, AFTER application of D frame
and bare coupling shift as required. Different powers per input weight after
MS expansion spelled out for real physical readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Lobby
open Function Finset Filter Topology Lattice Labels Source
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Plane
open MS.Land MS.Lifting MS.Local.Physical MS.Book.Convolve MS.Native.Studio MS.Native.Paint MS.Native.Wilsonian
open MS.Puff MS.Puff.Mom MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Dial MS.Tide MS.Swirl MS.Swirl.Near MS.Fleet MS.Rake MS.Vista MS.Vane
open PowerSeries (C coeff)
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation Precision Pert.Orb Billing
open scoped Topology BigOperators ContDiff PowerSeries
variable {G:Gauge}{d k:ℕ}{n:Side}{B:Deck G}{L:Frames G}{H:Hol G}
variable {W:Type} [LinearOrder W](D:ChartRatio G)(R:Lobby.Registry L H)
variable [Fintype W]
variable (K:MS.Land.Prescription B)(y:ℝ)(p:W→Rake.Label B)
local notation "pf"=> Table R B
local notation "g"=> Rake.Label.h∘p
local notation "PSc"=> PowerSeries ℂ
local notation "TC"=> redo K.team
local notation "∂"=> univ (α:=W)

abbrev wt (p:W→Rake.Label B):ℕ:= ∑ i:W,(p i).h
-- engineering compensation a=exp(-θ), multiply by a^-d.
def Paid (x:W→Site n)(ε:ℝ) (p:W→Rake.Label B): PSc := C ( (↑ε:ℂ)⁻¹ ^ wt p ) * WilsonPoint D R n x p

/-- Still OIL changes with rank/engineering scale. Multiply by TRUE dimensional adjustment before taking a limit. -/
def changePrice (ε:ℝ) (i:W)(j:χ p i): PSc:= C ( (ε:ℂ)^((j.size:ℤ) - (p i).h) ) * bore p K y i j

def newEra (x:W→Site n)(ε:ℝ): PSc := ∑ q:(i:W)→ Glyph B (p i).h, (∏ i,changePrice K y p ε i (q i)) * TC y (Paid D R x ε (fun i=> owner (q i)))
lemma tot_cost (x:W→Site n)(ε:ℝ)(he:ε≠0): newEra D R K y p x ε=C ((ε:ℂ)⁻¹ ^ wt p)*prepare D R K y p n x:=by
 unfold newEra prepare; rw [Finset.mul_sum]; refine sum_congr rfl fun q _=>?_; let u(i:W):= owner (q i); let U:= WilsonPoint D R n x u; let c:= C (R:=ℂ); let z:ℂ:=ε;
 rw [show TC y (Paid D R x ε u)=C ( z⁻¹ ^ wt u ) * TC y U from ?turn ]; swap
 · unfold Paid; rw [← PowerSeries.smul_eq_C_mul,map_smul,PowerSeries.smul_eq_C_mul]
 have h0:z≠0:=by unfold z; exact_mod_cast he
 unfold changePrice; rw [Finset.prod_mul_distrib]; have ht(q:W→Rake.Label B) : c (z⁻¹ ^ wt q)= ∏ i:W,c (z⁻¹ ^ (q i).h):=by rw [← map_prod c,Finset.prod_pow_eq_pow_sum]
 have hb : (∏ i:W, c (z^((u i).h-(↑(p i).h:ℤ))))*c (z⁻¹ ^ wt u)=c (z⁻¹ ^ wt p):= by
    rw [ht u,ht p,← Finset.prod_mul_distrib]; refine prod_congr rfl fun i _=>?_ ; rw [← map_mul, zpow_sub₀ h0, zpow_natCast,zpow_natCast, inv_pow, inv_pow]; congr 1; field_simp
 change (∏ i:W,c (z^((u i).h-(↑(p i).h:ℤ)))) * _ * (c _ * _)=c _ * _; rw [← hb]; ring
variable {A:Type}{T:Trial A W}{l:Filter A}{μ:ℝ}{M:Booked B}(S:MS_Data G M){X:Terrify W A}
set_option linter.unusedSectionVars false
abbrev spacing (T: Trial A W)(i:A):= Real.exp (-T.profile.θ i)
def situated (T:Trial A W)(i:A)(w:W): Site (dimT T.side i):= wrap _ (T.head i+T.off w i)
def evaluateR (T:Trial A W)(μ:ℝ)(k:ℕ)(i:A):= coeff k (newEra D R K (μ-T.profile.θ i) p (situated T i) (spacing T i))
open PeakT
lemma distanceT (hP:LocalRatio D) (hp: coherentPl M S pf p T μ true K l X)(i:A)(s:ℕ) (he:Admissible (dimT T.side i)) : fare g T.profile (ordZ X) ∂ s i= evaluateR D R K p T μ s i:= by
 have H: ordZ X (∂) s i= coeff s (prepare D R K (μ-T.profile.θ i) p _ (situated T i)):= congrFun (classicalμ ( τ_nil .. ) ( hp.cost i (∂)) ( paysHere D R (T.head i) (fun w=> T.off w i) K (μ-T.profile.θ i) p he hP )) s
 rw [fare,Pi.mul_apply,H,evaluateR,tot_cost _ _ _ _ _ _ _ (show spacing T i≠0 from (Real.exp_pos _).ne'),PowerSeries.coeff_C_mul ]; unfold higher Port.τ spacing; rw [ Real.exp_neg ]; rw [show ( ↑(Vane.charge (Rake.Label.h∘p) univ):ℤ)=↑(wt p) from rfl,zpow_natCast, Complex.ofReal_pow,Complex.ofReal_inv,inv_inv]
lemma twins (h:LocalRatio D) (hu:Dial.Uses T l μ) (hx: coherentPl M S pf p T μ true K l X) (k:ℕ): PeakT.twin l T.profile mildG (evaluateR D R K p T μ k) (fun i=> tour S p μ (testP T i) ∂ k):= by
 obtain ⟨hS,hV⟩:= hx.bouquet (∂) k; refine ⟨hS, PeakT.fromζ hV ?_⟩; filter_upwards [SideFunding hu] with i hi; rw [Pi.sub_apply,Pi.sub_apply,distanceT D R K p S h hx i k hi]
structure RangePl (D:ChartRatio G)(K: MS.Land.Prescription B)(W I:Type)[LinearOrder W][Fintype W] (T:Trial I W)(l:Filter I)(μ:ℝ)(p:W→Rake.Label B): Prop where
 pay (k:ℕ): twin l T.profile mildG (evaluateR D R K p T μ k) (fun i:I=> tour S p μ (testP T i) univ k)
 limit {f:W→QP}: Injective f→ Tendsto (testP T) l (𝓝 f) → ∀ k, Tendsto (evaluateR D R K p T μ k) l (𝓝 (tour S p μ f univ k))
lemma pays_all (h:LocalRatio D) (hu: Dial.Uses T l μ)(hg:G.Simple)(hk:TaylorOKPl S pf K) : RangePl R S D K W A T l μ p:=by
 obtain ⟨X,hx⟩:= Dial.check_tPl S pf p T hk hu hg true; refine ⟨twins D R K p S h hu hx, fun {f} hf ht k=>?_⟩; exact Dial.agrees _ (twins D R K p S h hu hx k) hu.upright ((Dial.contin S p f hf ∂ k μ).1.tendsto.comp ht)

theorem top_comparison (h:LocalRatio D)(hg:G.Simple): ∃ K : Prescription B,TaylorOKPl S pf K∧ ∀ (W A:Type)(_ :LinearOrder W)(_ :Fintype W) (T:Trial A W)(l: Filter A)(μ:ℝ)(p:W→Rake.Label B),Dial.Uses T l μ→ RangePl R S D K W A T l μ p:= by
 obtain ⟨K,hK,_⟩:= LPT_to_MSPl (Table R B) S hg; exact ⟨K,hK,fun W A _ _ T l μ p hu=>pays_all D R K p S h hu hg hK⟩
end YM.FVAAlt2.Lobby
