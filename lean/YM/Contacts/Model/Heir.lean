import YM.Contacts.Model.Piston
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma shovels (A:ℝ){f:E→ℝ}(h:AnalyticAt ℝ f 0) (v:ℕ)(x:E) : jet (A • f) v x=A* jet f v x:= by unfold jet; erw [iteratedFDeriv_const_smul_apply h.contDiffAt]; change _ * (A* _) = _; ring_nf; try rfl
end
-- low exact
section low
open Lintel.Plata Convoy Work.F05
variable {X:G.ColorIndex}{P:Bed}(B:BudgetPoint)(F:bore G)(hG:G.Simple)(he:Aegis X F P)
variable {A C Λ μ:ℝ}(p:Clip)(R:PathData G)(hR:R.Bounds p μ C Λ) {D: Stars→Side}(Q:∀ i:Stars,(D i).val=2*(ℓ+i.val))
-- only i+2<k+3 model needed; convenient skip i≥k+1 exactly treating those terms as zero. Because wind only ranks ≥2 & scales.
include hG he hR
lemma arm_vanish (x:Link G m)(hl:i+j<k+3)(hp:i+j<5 ∨ j<2)(h:Lintel.Plata.Dial P p R m)(ht:Orbit R (hair F m) p) : jet (anchor p R F m (k+3) i ∘ input G m) j x=0:= by
   change jet (moon F m (k+3) i - base p R m i ∘ input G m) j x=0
   rw [Ion.jet_minus _ (base p R m i ∘ input G m) _ _ (glowstar (should he.blazing) _ _ _ (by omega)|>.analytic) (armor_apt p R hR _),sub_eq_zero, certifiedStar (should he.blazing) m k i (by omega) x]; let T:= hair F m; rw [Nat.add_comm j i] -- twice?
   symm; by_cases hr:j<2
   · suffices hs : (if 2 ≤ i+j then design (hair F m (i+j-2) j) x else 0)=0 by
        rw [hs]; unfold base; split
        · exact (jet_bridge (show AnalyticAt ℝ (mainTerm p R ∘ input G m) 0 from armor_apt p R hR 0)).1 h.supports x j hr
        split
        · exact (jet_bridge (turns_analytic R.loop hR.width hR.two)).1 (turns_low _ hR.width hR.two) x j hr
        exact Convoy.jet_empty j x
     split; rw [hair_quiet he m hG _ _ hr,Forge.parcel_nil]; rfl
   unfold base; rw [if_pos (by omega : 2 ≤ i+j)]; split
   next hx=> subst i; exact (ht.draw j (by omega) (by omega) x).trans (if_pos (by omega : 2 ≤ 0+j))
   split
   next hx=> have hz:j=2:=(by omega); subst j i; exact ht.after x
   next hx hv=> rw [show hair F m (i+j-2) j=0 from mild_plat he.grade m _ _ (by omega),Forge.parcel_nil]; exact Convoy.jet_empty j x
variable (hh:∀ i,Dial P p R (D i)) (hv:∀ i,Orbit R (hair F (D i)) p)
omit hG in
lemma energy_apt (hk:i<k+3)(x:Site m) : altitude (pass (energy p R F Q (k+3) i) m x):= adapted_hue (fun _=>modulates _ _ (fun _=> anchor_apt p R F hR he hk) _) x -- hG not used
include hh hv
lemma eroded (x:Link G m)(ho:i+j<k+3)(hp:i+j<5 ∨ j<2)(y:Site m) : jet (pass (energy p R F Q (k+3) i) m y ∘ input G m) j x=0:= by
   let v:= Model.clock Q (fun t=>anchor p R F (D t) (k+3) i)
   -- apply jet scalar composition with family
   have ht (m:Side)(t:Stars): altitude (anchor p R F (D t) (k+3) i):= anchor_apt p R F hR he (by omega)
   let f (m:Side) (o:Site m):= pass v m o ∘ input G m; have he (m:Side)(o:Site m): AnalyticAt ℝ (f m o) 0:= modulates Q _ (ht m) o
   let Z (s: Signed):= f m (s⁻¹.act y) ∘ orderTurn s; have hz (s): AnalyticAt ℝ (Z s) 0:= Forge.starts _ (he m (s⁻¹.act y)) _
   change jet (pass (hue v) m y ∘ input G m) j x=_; rw [show pass (hue v) m y ∘ input G m= VerifiedReset.factor • (fun u=>∑ i:Signed,Z i u) from (by ext x; change pass (hue v) m y (input G m x)=_; rw [citizen_hue]; simp_rw [fitted_at]; rfl), shovels _ (ContDiffAt.analyticAt (ContDiffAt.sum fun i _=> (hz i).contDiffAt))] -- lemma
   rw [loan_sum _ fun i _=>hz i]; refine mul_eq_zero.mpr (Or.inr (sum_eq_zero fun i₁ _=> ?_)); let o:= i₁⁻¹.act y; rw [show jet (Z i₁) j x=_ from woven (he m o) (orderTurn i₁) x j]; let P (t: Stars) := anchor p R F (D t) (k+3) i ∘ input G (D t); let U (t:Stars):= P t ∘ denial (Trio.pad Q t) o; have hx : f m o=fun y=>∑ t:Stars, Slide.ray t* U t y:=by funext y; exact Finset.sum_congr (s₂:=(univ:Finset Stars)) (g:=fun t=> Slide.ray t*U t y) rfl fun t _=> congr_arg (fun x=> Slide.ray t* anchor p R F (D t) (k+3) i x) (okn _ _ y)
   have hU t: AnalyticAt ℝ (U t) 0:= Forge.starts _ (ht m t) _
   rw [hx]; erw [loan_sum _ fun i _=> analyticAt_const.mul (hU i)]; refine sum_eq_zero fun t _=>?_ ; let x':= orderTurn i₁ x; change jet (Slide.ray t • U t) j x'=0; rw [shovels _ (hU t),show jet (U t) j x'= _ from woven (ht m t) (denial (Trio.pad Q t) o) x' j, arm_vanish F hG ‹_› p R hR _ ho hp (hh _) (hv _), mul_zero] -- `he` shadow & P unfolds
end low
namespace Slope
open StressFlux (sign)
open Averaging (axes01)
variable {a b: ℝ}{B:BudgetPoint}{V:Offer G m}{q r:ℕ} (hm:m.val=2*r) (hz:2≤z)(hu:10*z< m.val)
variable (hG:G.Simple)(hv:Mirrors V)(hr:∀ i,B.Regular (neighbors z i) (V i))
    (hf:∀ i,altitude (V i)) (hx:∀ i,B.supBounds i (neighbors z i) (V i) b)
include hG hv hr hf hx hm hz hu
def hat (X:G.ColorIndex) (q:Offer G m): ℝ:= 2*jet (plays q) 2 (bolt r X)
lemma call (X:G.ColorIndex) : ‖hat X (r:=r) V-(Fintype.card (Site m):ℝ)*deposit V‖ ≤(charge z:ℝ)* rate m * (2*(b/B.threshold^2)):= by
   let x:= drive (m:=m) r X; let f (i:Site m):= logHessian (V i) x x; have hb:0≤b:=(hx 0).1; have he:B.threshold^2>0:=sq_pos_of_pos B.threshold_pos
   have ho o: coeff (V o) o axes01 axes01=deposit V:= by have h:= holder hG hr hz hu hv o axes01 axes01; rw [if_pos rfl,VerifiedReset.projection, plus_no z o hz,show (addr z o).site=o from rfl,if_pos (holds z o hu)] at h; exact h
   have ha: ‖deposit V‖≤b/B.threshold^2:= by apply (le_div_iff₀ he).2; rw [mul_comm]; exact coeff_diagonal hG (hr 0) (hx 0) _
   rw [show hat (r:=r) X V= ∑ i:Site m,f i from ?_,show (∑ i:Site m,f i)- _ = (∑ i:Site m,(f i-deposit V)) from ?_]; swap; · rw [sum_sub_distrib,sum_const,nsmul_eq_mul, card_univ]
   · refine sizeBay hm _ (fun x hl=>sub_eq_zero.mpr ((shine X hm hG (hr x) (by omega) hu hl).trans (ho x))) (by positivity) ?_; intro i; exact (norm_sub_le ..).trans ((add_le_add (rally X hm hG (hr i) (by omega) hu (hx i)) ha).trans_eq (two_mul _).symm)
   unfold hat; erw [loan_sum _ fun i _=> hf i,Finset.mul_sum]; exact sum_congr rfl fun i _=>(pumps r X hG (hr i) (hf i)).symm
omit hv hf hx hr
variable {X:G.ColorIndex}{P:Bed}{B':TableFee}(F:bore G)(he:Aegis X F P)
variable {σ:ℝ≥0}{A C Λ μ Z:ℝ}(p:Clip)(R:PathData G)(hR:R.Bounds p μ C Λ) {D: Stars→Side}(Q:∀ i:Stars,(D i).val=2*(ℓ+i.val))
variable (H:∀ v:Site m,B.Regular (neighbors z v) ((pass (energy p R F Q (k+3) i) m) v))
include hR he H
lemma concession (hk:i<3)(ho:i≤k) (hv:∀ t,Lintel.Plata.Dial P p R (D t)) (hr:∀ t,Lintel.Plata.Orbit R (hair F (D t)) p): deposit ((pass (energy p R F Q (k+3) i) m))=0:= by
   -- saw eo only if bank r etc; use specifically x.val=z. r=m.val/2≥ 2z
   let o :Site m:= fun _=>(z:Per m); have hx: openBank r z (o 0):=Or.inl (by unfold o; rw [ZMod.val_natCast_of_lt (by omega)]; omega); let u:=drive (m:=m) r X; let h:= holder hG H hz hu (reflects _ (paints _)) o axes01 axes01; rw [if_pos rfl,VerifiedReset.projection,plus_no z o hz,show (addr z o).site=o from rfl, if_pos (holds z o hu)] at h; change coeff _ o _ _=_ at h; rw [← h, ←shine X hm hG (H o) (by omega) hu hx, pumps r X hG (H o) (energy_apt F he p R hR Q (by omega) o), eroded F hG he p R hR Q hv hr _ (by omega) (by omega) o,mul_zero]
def finale (B:BudgetPoint)(m:Side)(z r:ℕ)(G:Gauge)(D: Stars→Side)(p:Clip)(b Z μ C Λ A σ:ℝ)(w k:ℕ):= ((charge z:ℝ)*rate m*(2*(b/B.threshold^2))+ 2*(upPrice G D p Z μ C Λ A σ w (k+3) 2 m*(r:ℝ)^2+ 2⁻¹*rate m*swell_price σ A))/(Fintype.card (Site m):ℝ)
lemma wind_price (hx:∀ v,B.supBounds v (neighbors z v) ((pass (energy p R F Q (k+3) i) m) v) b)(hk:3 ≤ i)(ho:i≤k)(hZ:PaintSupply G 2 Z)(hs:0<σ)(hw:Tills (k+3) σ A F)(hc:4*(w+1)+16≤ m.val)(hl:2*(w+1)≤ℓ)(ha:3≤w): ‖deposit (pass (energy p R F Q (k+3) i) m)‖ ≤finale B m z r G D p b Z μ C Λ A σ w k := by
   let v:=upPrice G D p Z μ C Λ A σ w (k+3) 2 m; let Y:= pass (energy p R F Q (k+3) i) m; let L:= anchor p R F m (k+3) i ∘ input G m; let u:Link G m:=bolt r X; let z':=jet L 2 u; have hf: L= moon F m (k+3) i:= by funext y; unfold L anchor base; erw [Function.comp_apply,Pi.sub_apply,if_neg (by omega : i≠0),if_neg (by omega : i≠2),Pi.zero_apply,sub_zero]; rfl
   have heQ: z'=design (hair F m i 2) u:= by unfold z'; rw [hf, certifiedStar (should he.blazing) m k i (by omega) u,if_pos (by omega : 2≤ 2+i), show 2+i-2=i by omega]
   obtain ⟨s,h',B'',hd⟩:= he.price; let ψ (j):= (should he.blazing).my.here j i 2
   have ht := polarized (q:=F i 2) (p:=hair F m i 2) (hw.cap i 2 (by omega) (by omega)) (printFeeds (heritage ψ m)) ψ (Exterior.coord 1,X) hm hs (salute hG X (should he.blazing) hd h' i (he.honor i (by omega)))
   let e:= charge z; let g:=Fintype.card (Site m); let c:ℝ:=2⁻¹*rate m*swell_price σ A; have hz : ‖z'‖≤ c:=heQ.symm ▸ ht
   have hv := call hm ‹2≤z› hu hG (V:=Y) (reflects _ (paints _)) H (energy_apt F he p R hR Q (by omega)) hx X
   have hu₁ :=transforms p R F hR hw he hG Q hZ B hc ha hl u (by omega : 2+i<k+3); let m':=jet (plays Y) 2 u
   have hu₂: ‖m'‖≤ v*(r:ℝ)^2+c:= by
      rw [show m'=m'-z'+z' from (sub_add_cancel ..).symm] -- changes rhs?;
      have hQ:0≤v:= by
         have h:=hw.nonneg; have he:= sumFee_nn p (G:=G) (μ:=μ) (C:=C) (Λ:=Λ) (k:=2) (Z:=outerCost G 2 Z); unfold v upPrice inkjet Model.pole; positivity
      exact (norm_add_le ..).trans (add_le_add (hu₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ticket r X hm) _) hQ)) hz)
   unfold finale; rw [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]; change ‖deposit _‖*(g:ℝ)≤ _; rw [mul_comm _ (g:ℝ),← show ‖(g:ℝ) * deposit Y‖= (g:ℝ)*‖deposit Y‖ from (norm_mul _ _).trans (congr_arg (fun p:ℝ=>p*‖deposit Y‖) (by simp))]; refine le_trans («b»:=‖hat X (r:=r) Y-(g:ℝ)*deposit Y‖ + ‖2*m'‖) ?_ (add_le_add hv ?_); swap; · rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]; exact mul_le_mul_of_nonneg_left hu₂ (by norm_num)
   rw [show hat X (r:=r) Y=2*m' from rfl,norm_sub_rev]; exact le_trans (le_of_eq (congr_arg norm (sub_add_cancel ((g:ℝ)*deposit Y) (2*m')).symm)) (norm_add_le ..)
end Slope
end YM.Contacts.Model
