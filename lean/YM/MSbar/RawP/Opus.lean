import YM.MSbar.RawP.Wind
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open AnalyticBridge.SectorAffine.Offset
variable {G:Gauge}{n:Side}{σ E ι:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype σ]
open AnalyticBridge.SectorAffine Metric Pressure
variable {G:Gauge}{n:Side}
variable {p:ℕ}{a b C K r:ℝ}
local notation "W"=> Positions (Primary n G)
local notation "ℓ"=>Measuring.chart n G
variable {Z B:ℝ}{k:ℕ}{c:Clip}{R:PathData G} (s:Signed)(q:Face (Per n))(b':Site n)
variable {S:Set (Positions (Primary n G))}{x:Positions (Primary n G)}
variable (h:Wind G a Z p) (hs:‖x‖<1)
local notation "ψ"=>Measuring.chart n G
variable (hR:R.Bounds c (a+2*b*p) C r)(hb:0≤b)
local notation "T"=> R.ellTerms q
set_option quotPrecheck false
local notation "L"=> affine s 0 q.1
include h hR hb hs
lemma opus : let Y(x:W) := R.ell (sparkP s x) q
             Through p Y x (Z*C) ∧ Beacon (Measuring.chart n G) b p Y L x (Z*C*Real.exp (b*p)):=by
    let B(i:ℕ):= R.row q.2 i; let t(i:ℕ) := |(B i).1| * Real.exp ((a+2*b*p)*(B i).2.length); let vu:=Real.exp (b*p)
    let U(i)(x:W):= R.ellTerms q i (sparkP s x); let f(i:ℕ):= Z*t i; let g(i:ℕ):= f i *vu
    have hc(p:W):(p∈ball (0:W) 1 ↔ ‖p‖<1):=by simp
    have hi(i:ℕ)(x:W)(hx:x∈ ball 0 1) : Through p (U i) x (f i) ∧ Beacon (Measuring.chart n G) b p (U i) L x (g i):=by
        let y:=(B i).1; let X:=(B i).2; let Y:=X.length
        let hv:= (h.2 n (B i).2 s q.1 _ ((hc x|>.1 hx).le)).smul (B i).1 
        have he : |(B i).1| *(Z*Real.exp (a*Y)) *Real.exp (b*(p*(2*Y+1):ℕ))=g i:=by unfold g f vu t; push_cast; nth_rw 1 [show |(B i).1| * (Z*Real.exp _) *Real.exp _= Z*|(B i).1| * (Real.exp (a*Y)*Real.exp (b*((p:ℝ)*(2*Y+1)))) from by ring]; rw [← Real.exp_add,show a*Y+b*(↑p*(2*Y+1))=(a+2*b*p)*Y+b*p from by ring,Real.exp_add]; unfold Y X; ring
        have h₀ : |(B i).1| *(Z*Real.exp (a*Y))≤ f i:=by
             have h:0≤Z:=h.1; unfold f t; rw [← mul_assoc,← mul_assoc, mul_comm _ Z]; gcongr; linarith only [mul_nonneg hb (Nat.cast_nonneg (α:=ℝ) p)]
        have hs: Requests Set.univ (U i) (Measuring.chart n G) L (2*Y+1):=fun x hx y hy he=> congr_arg ((B i).1 • ·) (supplyR s X q.1 x hx y hy he)
        refine ⟨Through.control ((show Allows p (U i) x (|(B i).1| *(Z*Real.exp (a*Y))) from hv).mono h₀), (show Beacon (Measuring.chart n G) b p _ _ _ _ from ?_)⟩; exact (hv.beacon hs Filter.univ_mem hb).mono he.le
    have hu:=hR.rows q.2; have hf:Summable f:=hu.2.1.mul_left _; have hg:∑' i,f i ≤ Z*C:=by unfold f; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hu.2.2 h.1
    have ht:=topS isOpen_ball (convex_ball ..) (fun i x hx=>(hi i x hx).1) hf x ((hc x).mpr hs); intro Y; refine ⟨ht.mono hg, Beacon.mono (cargo U f g isOpen_ball (convex_ball ..) (fun i x hx=>(hi i x hx).1) (hc x|>.mpr hs) hf (hf.mul_right _) (fun i=>hi i x (hc x|>.mpr hs)|>.2)) ?_⟩; unfold g; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hg (Real.exp_pos _|>.le)
variable (hP:PaintSupply G p K)
noncomputable def penG (G: Gauge) (q:Face (Per n))(s:Signed) (x: Positions (Primary n G)):= G.price (faceValue (sparkP s x) q)
noncomputable def priceA (G:Gauge)(p:ℕ)(K:ℝ):= priceCost G (travelCost G p 4 (outerCost G p K))
omit h hR
include hP
lemma earns : Beacon (Measuring.chart n G) b p (penG G q s) L x (priceA G p K * Real.exp (b*(p*5:ℕ))) :=by
    let w:= square q.2.val.1 q.2.val.2; have ht:(4:ℕ)=w.length:=rfl
    let u(v:W):=faceValue (sparkP s v) q
    have hv: Allows p (fun v=>G.mat (u v)) x (travelCost G p 4 (outerCost G p K)):=travel_jets (U:=fun v:W=>sparkP s v) (fun i=> votes s i _ hP hs.le) (w:=w) q.1 ht.ge
    exact (hv.price (f:=u)).beacon (fun a ha z hz he=> congr_arg G.price (whirls s w q.1 (p:=5) (by omega) a (Set.mem_univ _) z (Set.mem_univ _) he)) Filter.univ_mem hb
noncomputable def coinP (e:G.Color):= ‖e‖^2/2
omit hs hb hP in
lemma sq_supply (G:Gauge)(z:ℝ)(p:ℕ) :∃ B:ℝ,0 ≤B∧∀v:G.Color, ‖v‖≤ z→ Allows p coinP v B:=by
   -- function cont diff globally
   let f:= @coinP G; have hv(v:G.Color): ContDiffAt ℝ ω f v:= ((contDiff_norm_sq ℝ).div_const 2).contDiffAt; obtain ⟨B,hB,h⟩:= exists_allows (isCompact_closedBall (0:G.Color) z) (fun v _=> hv v) p; exact ⟨B,hB,fun x hx=> h x (by simpa using hx)⟩
include h hR
noncomputable def bucket (p:ℕ)(V C Z:ℝ) := (∑ i∈Finset.range (p+1), (Fintype.card (OrderedFinpartition i):ℝ))*(V*(1+C*Z)^p)
lemma earning (δ:ℝ)(hV:∀ v:G.Color, ‖v‖ ≤ Z*C→ Allows p coinP v δ): let f(v:W):=c.direct*penG G q s v+‖R.ell (sparkP s v) q‖^2/2
     Beacon (Measuring.chart n G) b p f L x ((|c.direct| *priceA G p K)*Real.exp (b*(p*5:ℕ))+bucket p δ (Z*C) (Real.exp (b*p))) :=by
    let Y(v:W):= R.ell (sparkP s v) q; let P:= penG G q s; let v:=Real.exp (b*(p*5:ℕ)); obtain ⟨hY,hQ⟩:=opus s q h hs hR hb; let g(x:G.Color):= coinP x
    have hp: Allows p (fun x:W=> G.mat (faceValue (sparkP s x) q)) x (travelCost G p 4 (outerCost G p K)):=travel_jets (U:=fun v:W=>sparkP s v) (fun i=> votes s i _ hP hs.le) _ (le_refl 4)
    have ht: ContDiffAt ℝ ω Y x:= Work.F02.ell_contDiffAt hR _ (fun z=> (votes s z x hP hs.le).analytic); let E:=c.direct • P; have hE: Allows p E x (|c.direct| * priceA G p K) := (hp.price (f:=fun x:W=> faceValue (sparkP s x) q)).smul c.direct
    have hu:‖Y x‖ ≤ Z*C:=(norm_iteratedFDeriv_zero (𝕜:=ℝ)).symm.trans_le (hY.pay 0 (Nat.zero_le _)); have hC:0 ≤ Z*C:= (norm_nonneg _).trans hu
    have hS:=Beacon.comp ht hQ (mul_nonneg hC (Real.exp_pos _|>.le)) (hV (Y x) hu); intro f; apply Beacon.add hE.1 ((hV (Y x) hu).analytic.comp x ht) _ hS; exact hE.beacon (s:=Set.univ) (r:=5) (fun a _ y _ he=> congr_arg (fun V:G.El=> c.direct*G.price V) (whirls s (square q.2.val.1 q.2.val.2) q.1 (p:=5) (le_refl _) a (Set.mem_univ _) y (Set.mem_univ _) he)) Filter.univ_mem hb
end YM.MSbar.RawP
