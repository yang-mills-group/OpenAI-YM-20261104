import YM.AllOrder.Rosary.Uniform
import YM.AllOrder.Wheel.Slip
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/-! Pole & Estimate budgets billed after L. Coarse T.cost=up betaHat(s) or down exactly (for simplicity). -/
namespace Repair
open Push PriceCompiler Floe Floe.Step Floe.Pace Floe.StateE Floe.Step.PlanV Plateau PhysicalNext.Repeat Pressure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Catch Catch.Clock -- maybe remove
open Tilt
-- Cost ratio for nearby betas. Payout via Search lease. Includes weighted difference with all mask.Finance.
local notation "Z"=>Real.exp
section
variable {A:Catch.Clock ι} {b c x:ι→ℝ}{y:ℝ}
local notation "T"=> A.rail
local notation "H"=> A.Meter
local notation "s"=> fun i=> (gStep (c i))
local notation "r"=> fun i=> (gStep (b i))
local notation "To"=> A.cost
lemma cool (f:ℝ→ℝ)(h:Rate G (1:Side) y f):H (f∘ To) y:= by
 let H':Aux.Looks G (1:Side) A (To):= ⟨A.drive,Eventually.of_forall (fun i=>(Burn.hat_this G (To i)).symm)⟩; exact Aux.Looks.bill H' h
-- pow and diff products.Lag all orientations. Φ extra price.
structure Compare (S:Catch.Clock ι)(b c:ι→ℝ)(y:ℝ):Prop where
 part : ∀ᶠ i in S.rail, Burn.Near (S.cost i) (b i)∧Burn.Near (S.cost i) (c i)
 beta : S.Meter (fun i=> b i-c i) y
lemma hedge (G:Gauge) (h:∀ᶠ i in T,Burn.Near (To i) (b i)) : Wheel.Epoch A b := by
 let f' : Aux.Looks G (1:Side) A (To):= ⟨A.drive, Eventually.of_forall (fun i=> (Burn.hat_this G (A.cost i)).symm)⟩ -- G not in Epoch! lemma adds explicit?
 obtain ⟨hz,hZ⟩:= f'.costs (show ∀ᶠ i in T,Burn.Near (Pressure.betaF G (To i) (1:Side)) (b i) from (by simp_rw [hat_this]; exact h)) f'
 have hv:∀ᶠ i in T,0< b i:= (A.positive.and h).mono fun i ⟨hh,ht⟩=> (div_pos hh (by norm_num : (0:ℝ)<4)).trans_le ht.1
 refine ⟨hv,Meter.smaller ((Meter.pale A 1).lscale (4:ℝ)) ?_,hz,hZ⟩
 filter_upwards [h,hv] with i hi hk; rw [abs_of_pos hk]; rw [Real.rpow_one]; exact hi.2.trans (le_abs_self _)
-- product_telescope
private lemma enjoy (k:ℕ) (h:H b C)(he:H c C) (hx:H (fun i=> b i-c i) y): H (fun i=> (b i)^k-(c i)^k) (C*(k-1:ℝ)+y):= by
 induction k with
 | zero=>simp; exact Meter.nil A _
 | succ k ih=>
   refine (Meter.add ((hx.mul (h.pow k)).weak ?_) ((he.mul ih).weak ?_)).eq_mem (Eventually.of_forall fun x=>?_)
   · push_cast; linarith
   · push_cast; linarith
   dsimp only; simp_rw [pow_succ]; ring
namespace Compare
variable (hp:Compare A b c y)
include hp
-- diff r−s=(c−b)*r²*s²/(r+s)
variable (G)
local notation "b!" => (fun i=> b i-c i)
include G
lemma response : H (fun i=> r i-s i) (y-3/2) ∧ H (fun i=> (r i)⁻¹-(s i)⁻¹) (y-1/2):= by
 let hx:= hp.beta; let hr:= hedge G (hp.part.mono fun i hi=>hi.1); let hs:=hedge G (hp.part.mono fun i hi=>hi.2); have hℓ: H (fun i=> (r i+s i)⁻¹) (1/2:ℝ):=Meter.smaller hr.starts (by filter_upwards [hr.one,hs.one] with i hi hh; have he:= Fare.gS (b i) hi |>.1; have ht:= Fare.gS (c i) hh|>.1; rw [abs_of_pos (inv_pos.mpr (by linarith)),abs_of_pos (inv_pos.mpr he)]; apply inv_anti₀ he; linarith)
 have h₀:H (fun i=> r i-s i) (y-3/2):= by
    let r':= r; let s':= s; refine (((((hx.neg.mul (hr.stepI.pow 2)).mul (hs.stepI.pow 2)).mul hℓ).weak (by norm_num; linarith))).eq_mem ?_; filter_upwards [hr.one,hs.one] with i hi he; have ⟨ha,hQ⟩:= Fare.gS (b i) hi; have ⟨hu,hL⟩:= Fare.gS (c i) he;  rw [← div_eq_mul_inv]; change -(_-_) * _ *_ / _ =_; rw [div_eq_iff _]; swap; · exact (add_pos ha hu).ne'
    linear_combination - (gStep (c i))^2*hQ+(gStep (b i))^2*hL -- check Fare def
 refine ⟨h₀,(((h₀.neg.mul hr.starts).mul hs.starts).weak (by linarith)).eq_mem ?_⟩; filter_upwards [hr.one,hs.one] with i hi he; have hQ := Fare.gS (b i) hi|>.1; have hT:= Fare.gS (c i) he|>.1; field_simp; ring -- unfolds risky
lemma phase (i:Age): H (fun p=> rates (r p) i-rates (s p) i) ((i.r-i.e:ℝ)/2+y-1):= by
 let hr:= hedge G (hp.part.mono fun i hi=>hi.1); let hs:=hedge G (hp.part.mono fun i hi=>hi.2); obtain ⟨he,hV⟩:= hp.response G
 refine (((((enjoy i.e hr.stepI hs.stepI he).mul (hr.starts.pow i.r)).weak ?_).add (((hs.stepI.pow i.e).mul (enjoy i.r hr.starts hs.starts hV)).weak ?_)).eq_mem (Eventually.of_forall fun j=>?_)); · linarith
 · linarith
 dsimp only [Tilt.rates,ratioW]; simp only [inv_pow]; ring
end Compare
-- Price post.Lane.G.Stage: polynomial growth.W.Transfer.
def deo (G:Gauge)(P: BudgetPoint)(b c:ℝ)(k:ℕ)(X:Finset Age)(v:ℝ):ℝ:=∑ i∈X, |rates b i-rates c i| * Tilt.bill G P P.B i.r (authority k i v) -- mismatched var X!
variable {p:ι→BudgetPoint}(G)(W:Stage)
def Frost (T₀:Catch.Clock ι)(W:Stage)(p:ι→BudgetPoint):Prop:=∀ᶠ x in T₀.rail,Time.Same W (p x) ∧ (p x).B=radiusB (T₀.cost x)∧ (p x).threshold=temp (T₀.cost x)
lemma Compare.pledge (hp:Compare A b c y) (hq:Frost A W p) (k:ℕ)(g:Finset Age): H (fun i=> deo G (p i) (r i) (s i) k g (strengthP (To i))) (y-5/2):= by
 refine Meter.sum g ?_; intro i hi
 let h:= hp.phase G i; have h0 : H (fun x=> (radiusB (To x):ℝ)) 0:= cool (G:=G) _ Rate.radius_price
 have hv := Meter.pow (cool (A:=A) (G:=G) («f»:=Pressure.temp) (Burn.temp_rate (G:=G))) i.r -- f explicit keyword
 let C':= Next.Scheduling.Wages.startup G i.r W.power W.order; let d:= Next.Scheduling.Wages.grade i.r W.power W.order
 let L:= fun x=> Tilt.bill G (p x) (p x|>.B) i.r (authority k i (strengthP (To x))); have hz:H L (-(1/2:ℝ)*i.r):= by
    let hp:= (cool (A:=A) (G:=G) («f»:=fun x=> authority k i (strengthP x)) (Burn.first_rate (G:=G) i k)); let hh:= (hp.mul ((hv.lscale C').mul (((Meter.const A 1).add h0).pow d))).lscale (Push.Local.turnCost W.order W.power); refine (hh.weak (by linarith)).eq_mem ?_; filter_upwards [hq] with i ht; unfold L Tilt.bill; rw [ht.2.1, ht.2.2,ht.1.1,ht.1.2.1]; -- fL
    rfl
 exact (h.ab.mul hz).weak (by have h : (3:ℝ)≤ i.e:= Nat.cast_le (α:=ℝ)|>.mpr i.senior; linarith)
end
section
variable (s:Floe.Layout G) (B:Floe.Step.Fees) (hB:∀ i,0<B i) (b c x:ℝ)(k:ℕ)(i:Finset Age) (h:∀ j∈i,Quoted (s j) (B j) (authority k j x))
include h hB
-- fixes signed family & total (M' = pred−actual)
def err (s:Floe.Layout G) (u:ℕ)(i:Finset Age)(b c:ℝ): Burn.Locale G:= Tilt.sundry s u (fun j=> rates b j-rates c j) i
lemma repairs (g:G.Simple) (o:Site n)(he:4≤n.val)(hk:∀ j∈i,4*j.r≤p.B) : Fairness p o (court o p.B) (err s p.B i b c n o) (deo G p b c k i x):= Fairness.enroll i (fun j hi=> (Tilt.fair _ _ _ _ (h j hi) (hB _) (hk _ hi) (by unfold Age.r; omega) he g).scale (rates b j-rates c j))
omit h hB
open Finset
lemma pure (n:Side)(o:Site n) : err s p.B i b c n o= Burn.offerS G p s i b n o-Burn.offerS G p s i c n o:= by -- set u same p
 change _=(∑ k∈i, _ • _)-(∑ k∈i,_ • _); unfold err sundry; simp_rw [sub_smul,Finset.sum_sub_distrib]
end
end Repair
end YM.AllOrder.Rosary
