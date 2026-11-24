import YM.Contacts.Model.Tahoe
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
namespace Arbor
open Lintel.Plata ConnectedActivityE6 Next.Fluctuations Blaze Sienna
open Boulevard (actual throng stillA sunny)
open Slope (addr)
variable {A H Z t C Λ I μ:ℝ}{S:ℝ≥0}{d v:ℕ}{B:BudgetPoint}{X:G.ColorIndex}{P:Bed}{L:Side}
lemma confident {ι:Type}(F:ι→RegularAddress m) (B:BudgetPoint): Meadow.Budget (G:=G) B F 0 0 := by
    refine ⟨0,fun x=>?_ ,fun i=>⟨reg_const (0:ℝ),?_⟩⟩; · simp [SumBudget]
    change B.supBounds _ _ (fun _=>0) (0:ℝ); simpa using (CouplingShape.sup_const (p:=B) (o:=(F i).site) (X:=(F i).support) (G:=G) 0) -- def
structure Patron (G:Gauge)(B:BudgetPoint)(d σ:ℝ) (z:ℕ): Prop where
   positive:0<d
   scope:d<1
   interior (m:Side)(W: Positions (Push.Uniform.Primary m G))(f:Config G m→ℝ) (r:ℝ) :
     ‖W‖+σ<d→flags B.threshold (actual W)=∅→f 1=0→B.Regular univ f →(∀ V,‖V‖≤d → Brush B.order r d⁻¹ (f∘actual) V)→
     ∀ l:List (Directions G m), l.length≤B.order→(∀ i∈l,‖i‖≤B.threshold) → ‖leftDerivs f l (actual W)‖≤ Boulevard.ticket B.order r
   aspect : 0<σ
   sites (c f:Side)(h:2*z<c.val)(w:ℕ)(hv:w+1≤z)(hy:2*w≤f.val)(o:Site c) (V:Config G c) : Healthy B.threshold (neighbors z o) V→ ∃ (u:Site f→G.El) (P:Positions (Push.Uniform.Primary f G)), actual P=gauge u (Slide.shape (Slide.cognac hy) o V) ∧ ‖P‖+σ<d
lemma patrons (G:Gauge)(L:Side)(k:ℕ) (f:ℝ→ℕ)(h:Rate G L 0 fun x=>(f x:ℝ)): ∀ᶠ x:ℝ in atTop,∀ B:BudgetPoint,B.threshold= Pressure.temp x → B.threshold≤2*Pressure.fiery G x L→ B.order=k→ Patron G B (eaves G L x) (2*furl G L x) (f x):= by
   filter_upwards [Trio.pledges G L f h,Boulevard.rising G L k,Sienna.below' G L (Sienna.edge G L) Sienna.vow_ok zero_lt_one,Delay.shift_pos G L] with x hv hw hb hx B ht hh h'; have he:0<eaves G L x:=Real.rpow_pos_of_pos hx _; have hF:0<2*furl G L x:=mul_pos zero_lt_two (Real.rpow_pos_of_pos hx _); refine ⟨he,hb, fun m W f q hM hn hf hc hP l hl hL =>?_ , hF, hv B hh⟩; let p:= fun _:ℕ=> addr 0 (0:Site m)
   let y:= hw B ht hh h' m W hM hn p (0:ℕ→ Config G m→ℝ) f (-f) q 0 0 (confident p B) hc; have he: stillA f=f:= by ext x; simp [stillA,hf];
   have ha (v: Config G m) : -f v=0-f v-throng 0 v:=by simp [throng]
   have hQ: stillA (-f) = -f:=funext fun u=> by unfold stillA; simp [hf]
   have hU (V: Positions (Push.Uniform.Primary m G))(hv:‖V‖+2*furl G L x < eaves G L x) (hl: actual V ∈ sunny B): Brush k q (eaves G L x)⁻¹ ((stillA (-f)) ∘ actual) V:= by rw [← h',hQ]; exact (hP V (by linarith)).opposite
   have hy:= y (fun V _=> ha V) hU l hl hL; rw [he, ← h',mul_zero,mul_zero,add_zero] at hy; exact hy

variable (F:bore G)(p:Clip)(T:PathData G)(he:Aegis X F P)(hP:T.Bounds p μ I Λ)
variable {Y: Stars→Side}(Q:∀ i:Stars,(Y i).val=2*(ℓ+i.val))
variable (hG:G.Simple)(hv:∀ i,Dial P p T (Y i))(ha:∀ i,Orbit T (hair F (Y i)) p)
variable (hp:Tills (k+3) S C F)(hY:∀ i,(Y i).val≤v)(hx:i≤k)(hy:2≤k)
variable {σ:ℝ}(hh:Patron G B t σ z)(hc:2*z< m.val) (hA:ℓ+5≤z)
abbrev hero (i:ℕ):= max 2 (5-i)
lemma owned (i:ℕ):2≤hero i := le_max_left ..
lemma upper (i:ℕ):hero i≤5 :=max_le (by decide) (Nat.sub_le ..)
include he hP hG hp hx hy
variable (ht: Dial P p T n)(hW: Orbit T (hair F n) p)(hz:n.val≤v)
include ht hW hz hh
lemma roadway (X:ℝ)(hw:PaintSupply G B.order X)(hy':sufficient G v (holdOn B.order (outerCost G B.order X)) t)(y:Positions (Push.Uniform.Primary n G))(hv:‖y‖≤t): let d':= tollP G p v (k+3) B.order C (holdOn B.order (outerCost G B.order X)) μ I Λ; Brush B.order (d'*t^hero i) t⁻¹ (anchor p T F n (k+3) i ∘ actual) y:= by
    intro d'; have hB:= B.order_ge; let f:= anchor p T F n (k+3) i; have hf: altitude f:= anchor_apt p T F hP he (by omega)
    apply potCap (f:= f ∘ actual) (fun x hx'=> atEase (canyon hw n) T F he hG hp hz (by omega) hP t hh.scope hy' (mem_closedBall_zero_iff.mp hx') (by omega)) (fun x j hj=>?_) (by have hx:= upper i; omega) hh.positive hh.scope.le (mem_closedBall_zero_iff.mpr hv)
    rw [show actual (c:=n) (G:=G)=input G n ∘ settle n from funext (fun x=> (borne x).symm)]; erw [Garf.woven (F:=f∘input G n) hf (settle n) x j]; apply arm_vanish F hG he p T hP (settle n x) _ _ ht hW <;> unfold hero at * <;> omega
omit ht hW hz
include hv ha hY hA hc
def year (B:BudgetPoint)(z:ℕ)(f:ℝ):= (Push.Local.turnCost B.order B.power)*(Trio.oroW B z (fun _=> Boulevard.ticket B.order f))
lemma offered (x:Site m)(X:ℝ)(hw:PaintSupply G B.order X)(hy':sufficient G v (holdOn B.order (outerCost G B.order X)) t) : B.supBounds x (neighbors z x) (pass (energy p T F Q (k+3) i) m x) (year B z (tollP G p v (k+3) B.order C (holdOn B.order (outerCost G B.order X)) μ I Λ * t^hero i)):= by
    let S j:= anchor p T F (Y j) (k+3) i; let v' j := Site (Y j); let Z:= year; let q:= tollP G p v (k+3) B.order C (holdOn B.order (outerCost G B.order X)) μ I Λ*t^hero i; let Y' := Model.clock Q S; let o: Site m:=0; let w:=Push.Local.turnCost B.order B.power
    have hh' i: B.Regular univ (S i):= anchor_bill B F p T hP he (by omega) _
    have hK j: S j 1=0:= by have e':= arm_vanish F hG he p T hP (i:=i) (0:Link G (Y j)) (j:=0) (k:=k) (by omega) (by omega) (hv j) (ha j); simpa only [jet_zero,comp_apply,input_zero] using! e'
    have hS (j:Stars) (x: Positions (Push.Uniform.Primary (Y j) G))(he':‖x‖+σ<t)(hk:flags B.threshold (actual x)=∅) := hh.interior _ x (S j) q he' hk (hK j) (hh' j) (roadway F p T he hP hG hp hx hy hh (hv j) (ha j) (hY _) X hw hy')
    have hq : 0≤ Boulevard.ticket B.order q:= by
       have hs:0≤q:= (roadway F p T he hP hG hp hx hy hh (hv 0) (ha 0) (hY 0) X hw hy' (i:=i) 0 (by simp [hh.positive.le])).nonneg; unfold Boulevard.ticket; positivity
    have hH := regular_clock B Q (Y:=S) (show ℓ+4 ≤ z from by omega) hh' o
    have hX:B.supBounds o (neighbors z o) (pass Y' m o) (Trio.oroW B z fun _=>Boulevard.ticket B.order q):= by
       rw [show pass Y' _ o=∑ i:Stars,Slide.ray i • (S i ∘ Slide.shape (Trio.pad Q i) o) from funext fun _=> by rw [Finset.sum_apply]; rfl]; have hz i (x : Site (Y i)): separation o (Slide.sites (Trio.pad Q i) o x)≤ z:= (Slide.village (w:=ℓ+i.val) _ _ _).trans (by have hx:=i.isLt; omega)
       refine Trio.sup_S B _ _ _ _ _ (fun i _=> CouplingShape.reg_scale _ (Slide.regular (Trio.pad Q i) o (hh' i) (fun j => (neighbors_mem ..).2 (hz i j)))) (fun i _=> CouplingShape.sup_scale _ ?_)
       refine ⟨mul_nonneg (by unfold Trio.tilt; positivity) hq,fun V H l hl hD=> ?_⟩; obtain ⟨g,P,hP,hR⟩:= hh.sites m (Y i) hc (ℓ+i.val) (by have hx:=i.isLt; omega) (Q i).ge o V H; have hu:= Trio.hint Q z V i (show ℓ+4 ≤ z from by omega) o H; apply Slide.stalled (Trio.pad Q i) o (S i) (hz i) l V hl hD ((hh' i).smooth _ (by unfold Healthy; rw [hu]; simp)); have he:=hS i P hR (by rw [hP,gauge_flags]; exact hu); rw [hP] at he; exact Slide.bills g (hh' i).symmetry he
    let v0:= w*(Trio.oroW B z fun _=> Boulevard.ticket B.order q); have hf (i:Signed):B.Regular (neighbors z x) (lend Y' i x):= (tilt_share (z:=z) x i) ▸ (Seat.regular (i,x) hH)
    have hr (i:Signed): B.supBounds x (neighbors z x) (lend Y' i x) v0:= (tilt_share (z:=z) x i) ▸ (Seat.sup (i,x) hH hX)
    rw [show energy p T F Q (k+3) i=hue Y' from rfl,ties]; refine sup_le (CouplingShape.sup_scale _ (Trio.sup_S B _ _ _ _ _ (fun i _=> hf i) (fun i _=> hr i))) ?_; rw [sum_const,nsmul_eq_mul,card_univ,abs_of_nonneg VerifiedReset.factor_pos.le, ← mul_assoc, VerifiedReset.factor_card,one_mul]; exact le_of_eq rfl
end Arbor
end YM.Contacts.Model
