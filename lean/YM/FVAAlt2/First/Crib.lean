import YM.FVAAlt2.First.Glue
import YM.FVAAlt2.First.Meter
/-!
# Calibration relation.One (Science Pose). Real first derivative equals exactly canonical cTest after post pose.
Minimum triangle only (<*>). PP.Bank used here, one frame.Read-World charts, not final regulator choice. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.First.Portray
open Function Set Filter Finset Topology Lattice MeasureTheory
open Precision Extra.FD Maxwell Labels Extraction Matrix
open FormalOPE FormalOPE.RG10.Gazebo FormalOPE.RG10.Position FormalOPE.RG10.Carryon
open Pert Pert.Position PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle PertExtension.Physical
open Home Home.Profiles Home.Subsidy Report Tent Pairing SchemeConversionRG11
open scoped BigOperators Classical Topology PowerSeries Matrix
open RG10 (Through)
open Clockers Convert
open MS.Land
open PowerSeries (C coeff constantCoeff)
variable {G:Gauge}{F:Frames G}{m d n:ℕ}{q:Side}
local notation "K"=> deck F d
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation "V"=> RG10.Position.Deck F d
local notation "V₀"=> RG10.Position.Deck F 6
local notation "ZD"=> Datum V
variable (q)
open RG11.FirstW
lemma Debt_loan {A:Datum ( RG10.Position.Deck F d )→fps}{X Y:ℕ→Datum (RG10.Position.Deck F d)→fps}(v:Debt A m X) (h:∀ n i, Through m (X n i) (Y n i)): Debt A m Y:=by intro i j hj; exact (v i j hj).congr fun n=> h n i j hj
variable (hG:G.Simple)(Z:ℕ→Pack F)(hq:1<q.val){X : Stock F}(hO: Official X)
include hO
include hq in
lemma upright1 (B:Issue F 6) (H:Issue.Limits 1 atTop (FirstSap F q Z) B) (hk:B.Twist): Debt ((X 6).positioned (loot B)) 1 (fun i:ℕ=> post X (plunge F i q 6)):= by
 let Y:= X 6; let W(i:ℕ):= FirstSap F q Z i; let p(i:ℕ):= sap F q Z i 1; let c0 (i):= tic ( p i ); let U(i):= charge (c0 i).val
 refine revenue hO _ _ ( seal0 q Z B hq H (Or.inr hk)) U (fun i=> charge_Up _) (fun i=> charge_zero (c0 i).val) ?_ -- argument order
 apply Debt_loan (pursued H); intro i v; unfold U c0 p; rw [ ← amounts_loot q ]; exact (imprint_id (Issue.bareSide (F:=F) (d:=6) q i) (sap F q Z i) (tic _) (sap₀ ..) (honest ( sap F q Z i 1 )|>.symm) v).symm
omit hO
lemma warp_first {w:Warp}(he:coeff 1 w.x=1)(p:fps): Through 1 (w.charge p) p:= by
 intro i hi; interval_cases i; simp only [ PowerSeries.coeff_zero_eq_constantCoeff_apply ]; exact w.smoothed p
 rw [Warp.heats,he,mul_one]
variable (P:RG10.Position.Plan F)(hP:P.liftOff=LoftPP F)(μ:ℝ) {M:MS.Land.Booked (Home.seats P.liftOff P.certified)} (S:MS.Land.MS_Data G M)
local notation "sD"=> Home.seats P.liftOff P.certified
local notation "sE"=> science μ S F
local notation:max "τ_" i:max=> μ- Θ q i
variable (p:MS.Land.Prescription (Home.seats P.liftOff P.certified))
local notation "be"=> ( frameO F sD q )
variable (H:Launch (ExtraBook ( seats P.liftOff P.certified )) S (F:=F) p)
include H hq hP hO hG
variable {Q:ChartRatio G}(h:LocalRatio Q)
include h
lemma slow_price : Debt ((X d).positioned (sE d)) 1 (fun i:ℕ=> post X (plunge F i q d)):= by
 let B:= fun i:ℕ=> plunge F i q d; let U(i:ℕ):= frameO F sD q i μ p d
 have HZ(i:ℕ): (U i).map Ω=1:= Subsidy.ready q μ P hP S p h hG H.high hq d i
 have he(i:ℕ): Upright (U i):= by
    apply Upright.obtainable; · rw [ show Stg (U i) 0= _ from (by rw [show Stg (U i) 0= (U i).map Ω from Matrix.ext fun _ _=> PowerSeries.coeff_zero_eq_constantCoeff_apply _]; exact (HZ i) : Stg (U i) 0=(1: Matrix V V ℝ)), sub_self ]; exact Submodule.zero_mem _
    intro k hk; exact Convert.thigher μ q H hk -- type not Upright but Stage.
 refine revenue hO _ B (funext ( physics F μ S )) U he HZ ?_
 have hA : Debt (sE d) 1 (fun i=> employ i q μ P p d):=fun v j _=> Subsidy.measured_p q μ P hP S p h hG H.high hq v j
 apply Debt_loan hA; intro i v; let W: Warp:= ⟨ revise p.team (μ-Θ q i),revise_zer ..⟩
 let X₀:= W.charge ∘ B i
 have hx : Sync 1 X₀ (B i) v.1:= fun k=> warp_first (w:=W) ( revise_one .. ) _;
 unfold employ; change Through 1 (mix _ _ v) ( mix _ _ v ); rw [ show PowerSeries.subst (revise p.team (μ-Θ q i)) ∘ plunge F i q d = X₀ from funext fun k=> (W.turning (B i k)).symm ]; exact hx.send ( fun i j=> RG10.Through.refl ( U _ i j ) ) v.2
lemma same_pose (B:Issue F 6)(hB:B.Twist)(hX:Issue.Limits 1 atTop (FirstSap F q Z) B) (v:Datum V₀): Through 1 ((X 6).positioned (sE 6) v) ((X 6).positioned (loot B) v) := by intro i hi; exact tendsto_nhds_unique ( slow_price (P:=P) q hG hq hO hP μ S p H h v i hi ) ( upright1 q Z hq hO B hX hB v i hi ) -- order maybe
omit H hq hP hO h hG
-- collect post.Phase through 1
open Peal
-- names ground.
lemma one_grid (X:Stock F)(h:Official X) (B:Issue F 6) : ∃ b:ℕ→ Buffer F 6, b 0=0∧∀ v:Datum V₀, Through 1 ( (X 6).positioned (loot B) v ) (loot (Issue.imprint b B) v) := by
 let v:= loot B; let k i j:= (X 6).position v i j; let Y:V₀→V₀→ℝ:= fun i j=> coeff 1 (k i j); have hy: Y∈ tents F 6:= by rw [ ← RG10.Carryon.agree h ]; exact (X 6).positive_variation v 1 (by decide)
 let A:= (⟨Y,hy⟩: tents F 6); let b(j:ℕ): Buffer F 6:= if j=1 then buf A else 0
 refine ⟨b,if_neg (by decide),fun w:Datum V₀=>?_⟩; apply RG10.Through.trans _ ( imprint_id B b A (if_neg (by decide)) (if_pos rfl) w );
 have he(i j: V₀): Through 1 (k i j) ( charge Y i j ):=by
    intro d hd; interval_cases d; · simp_rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, k,TestSystem.position_zero,h.normal]; rw [show Ω _ = (1:Matrix V₀ V₀ ℝ) i j from congr_fun₂ (charge_zero Y) i j ];exact congr_fun₂ ( RG10.Carryon.diag_one (F:=F) (d:=6)|>.symm ) i j
    exact (congr_fun₂ (charge_1 Y) i j).symm
 exact Sync.send (b:=v) (c:=v) (fun t=> RG10.Through.refl _) he w.2 -- names likely bad
lemma touch_through {p q:Datum V₀→fps}(v:∀ i, Through n (p i) (q i))(s:Fin d ↪ Fin 3): Through n (touch F p s) (touch F q s):= RG10.Through.sums (fun i _=> (RG10.Through.refl _ ).mul (v _) )
lemma together_through {p q:Datum V₀→fps}(v:∀ i, Through n (p i) (q i)): Through n (together F p) (together F q):=
 (( touch_through v (.refl (Fin 3)) ).sub ( RG10.Through.sums (fun i _=> (touch_through v (Fin.succAboveEmb i)).mul (touch_through v ( Peal.single i )) ) ) ).add (( RG10.Through.refl _ ).mul (RG10.Through.prods (fun i _=> touch_through v ( Peal.single i ))))
-- consequence coupled.S.Pivot.
include h hG hP hO
lemma canonical_first (he : Spect F M) : coeff 1 (Peal.together F ((X 6).positioned (science μ S F 6)))=Peal.slope G:= by
 let q: Side:=2; have hq:1<q.val:=by decide
 obtain ⟨Z,HZ⟩:= RG11.FirstW.Deck.covers_r F (show RG11.FirstW.MarkGrid ( Pert.Align.itinerary q hq ) _ from fun i=>Rig.exchangePt q i ); obtain ⟨B,hB,hC,hV⟩:= RG11.FirstW.goes hG F hq Z HZ; obtain ⟨φ,hφ⟩:=Pairing.lpt_launch P S he hG; obtain ⟨b,hb,h⟩ := one_grid X hO B; obtain hx := together_through (fun i=> ( same_pose (p:=φ) (P:=P) q hG Z hq hO hP μ S hφ ‹LocalRatio Q› B hB hV i ).trans (h i)) 1 le_rfl; rw [hx,imprint_lit B b hG hB hb,hC, Peal.slope_value, Complex.ofReal_re]
end YM.FVAAlt2.First.Portray
