import YM.MS.ScaleForest.Screened
import YM.MS.ScaleForest.QuadraticLabel
import YM.MS.ScaleForest.Halves
import YM.MS.ScaleForest.AtOrigin
/-!
# A marginally improved parent with zero pole

Attaching the leading quadratic mark to ANY rank-2 bulk node by a tree
bridge with kernel vanishing at zero momentum gives no new pole to subtract, even if the bulk
node graph was
itself UV subtracted. It's its own subtraction rule (Jet tested on ALL
auxiliary m, including ghost-number inputs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Quadratic
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum XSpace XSpace.Chiral Cylinder
open scoped Topology ContDiff
variable {G : Gauge} {m d : ℕ} {p q:ℤ} (X:Pupil)
variable {F H: Mob G} {K:Rip G} {W:LocalVertex G false 4}
local notation "Iβ" => Name G

lemma antenna_sc (i:Name G)(s:L m)(c:G.ColorIndex)(p:SectorP m)(u:ℝ): antenna X i s c (u•p)=(u:ℂ)* antenna X i s c p:= by
   unfold antenna; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; unfold rampLeg polar0 Landau.delta; split_ifs <;> simp <;> ring

lemma mark_sr (p q : SectorP m)(a b:Cfield G m)(x:ℝ): (enrol X G 0).symbol m [(a,x • p),(b,x•q)]=(x:ℂ)^2 * (enrol X G 0).symbol m [(a,p),(b,q)]:= by
   let U := Uses_quad X (G:=G) m
   by_cases h : isA (G:=G) (a,p); swap; · rw [U _ (a,x•p) (by simp) h,U _ (a,p) (by simp) h,mul_zero]
   by_cases he: isA (G:=G) (b,q); swap; · rw [U _ (b,x•q) (by simp) he, U _ (b,q) (by simp) he,mul_zero]
   obtain ⟨i,s,H⟩:= h; obtain ⟨j,t,hE⟩:=he; change a=_ at H; change b=_ at hE; subst a b
   let W:= (enrol X G 0).symbol m; change W [vec i s (x•p),vec j t (x•q)]=(x:ℂ)^2 * W [vec i s p,vec j t q]; unfold W
   rw [takesA,takesA,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by simp only [weightedArm,antenna_sc]; ring

-- Here keep the full Koszul sign for other external tests (later pressure
-- formulas only evaluate gauge fields).
def slotTake (K : Rip G) (F H:Mob G) (i j:Cfield G m)(p q:SectorP m): ℂ:=
   ∑ a:Cfield G m,∑ b:Cfield G m,2*K m a b (-p) * (cross (parity b) (parity i)* F m [(a,-p),(i,p)])* H m [(b,p),(j,q)]

lemma branching (hr:Goods 2 F)(he:Goods 2 H)(K:Rip G)(i j:Cfield G m)(p q:SectorP m): bridgeG K F H m [(i,p),(j,q)] =
   slotTake K F H i j p q + cross (parity i) (parity j)*slotTake K F H j i q p:= by
    unfold bridgeG; simp only [scatter_cons,scatter_nil, degree, field]; simp_rw [ (show ∀ l:Shore G m, H m [l]=0 from fun l=>he m _ (by simp)), (show ∀ l:Shore G m,F m [l]=0 from fun l=>hr m _ (by simp) ), net_cons ]
    simp [slotTake,net]; exact add_comm .. 

private def paySlot (F H:Mob G)(K:Rip G)(i j:Cfield G m)(p q:SectorP m)(x:ℝ): ℂ:= ∑ a:Cfield G m,∑ b:Cfield G m,2*K m a b (-(x•p)) * (cross (parity b) (parity i)* F m [(a,-(x•p)),(i,x•p)]) * H m [(b,p),(j,q)]

private lemma slot_pay (p q:SectorP m)(i j:Cfield G m)(x:ℝ) :
   slotTake K F (enrol X G 0).symbol i j (x•p) (x•q)=(x:ℂ)^2 * paySlot F (enrol X G 0).symbol K i j p q x:= by
     unfold slotTake paySlot; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl fun b _=> ?_); rw [mark_sr]; ring

private lemma pay_smooth (he:rPrice K)(hu:kPrice F)(H:Mob G)(p q:SectorP m)(i j:Cfield G m): ContDiff ℝ ∞ (paySlot F H K i j p q):= by
    unfold paySlot; apply ContDiff.sum; intro a _; apply ContDiff.sum; intro b _
    let V(x:ℝ):= -(x•p); let U(c:Cfield G m)(x:ℝ):= F m [(c,V x),(i,x•p)]; have hU : ContDiff ℝ ∞ (U a):= by
        convert! (hu m ℝ (ray [(a,-p),(i,p)])).smooth () using 1; ext; simp only [U,V,fieldVal,ray_go,List.map_cons,List.map_nil,smul_neg]
    have hv : ContDiff ℝ ∞ (K m a b):= (he m a b 0).smooth ()
    refine (ContDiff.mul (?_) ((contDiff_const (𝕜:=ℝ)).mul hU)).mul contDiff_const
    exact (contDiff_const.mul (hv.comp (show ContDiff ℝ ∞ V by unfold V; fun_prop)))
private lemma pay_stop (he:∀ (i j:Cfield G m),K m i j 0=0)(H:Mob G)(p q:SectorP m)(i j:Cfield G m): paySlot F H K i j p q 0=0:= by simp [paySlot,he]

lemma jet_two (g:ℝ→ℂ)(hv:ContDiff ℝ ∞ g)(hh:g 0=0)(hn:d≤2) : reading d (fun x:ℝ=> (x:ℂ)^2 * g x)=0:= by
    let f(x:ℝ):=(x:ℂ)^2; have he : deriv f 0=0:= by
       unfold f
       rw [show (fun x:ℝ=>(x:ℂ)^2)=(fun x:ℝ=> (↑(x^2):ℂ)) from funext fun _=>(Complex.ofReal_pow ..).symm, HasDerivAt.deriv (HasDerivAt.ofReal_comp (hasDerivAt_pow ..))]; norm_num
    have hx: ContDiff ℝ (d:WithTop ℕ∞) f := by exact Complex.ofRealCLM.contDiff.pow _
    unfold reading; rw [iteratedDeriv_fun_mul hx.contDiffAt (hv.contDiffAt.of_le (by exact_mod_cast le_top))];
    have h0 : f 0=0:= by unfold f; norm_num
    change _ • (∑ i∈Finset.range (d+1), ((↑(d.choose i):ℂ) *iteratedDeriv i f 0 )* iteratedDeriv (d-i) g 0)=(0:ℂ)
    interval_cases d <;> simp [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one, he,hh,h0]

lemma mlength (l : Legs (Shore G m)) : (l.length:ℤ) ≤ mass l:= by
   induction l with| nil=>exact le_rfl
                   | cons i l ih=>
                     rw [Price_cons]
                     have he:1≤wfield i.1:= by rcases i with ⟨⟨⟨_|a,_|_⟩,b⟩,c⟩ <;> norm_num [wfield,dim]
                     simp; omega

lemma jetArm (he:HalfKernel K) (hu:∀ (m:ℕ)(i j:Cfield G m),K m i j 0=0) (hF: Goods 2 F)(hp:kPrice F) : Tad (bridgeG K F (enrol X G 0).symbol) 4=0:= by
   funext m l; let H:=(enrol X G 0).symbol; have hH:Goods 2 H:= (enrol X G 0).slots
   by_cases hL:l.length=2; swap
   · unfold Tad skin; split
     · rw [torch_at]; simp_rw [ show ∀ x:ℝ, bridgeG K F (enrol X G 0).symbol m (sail (ray l) x)=0 from fun x => ranks_off (bridge_rank' hF hH K) _ (by rw [ray_go,List.length_map]; omega)]
       simp [reading]
     rfl
   by_cases hz: (4:ℤ) < mass l; exact t_exc hz
   let d:= (4-mass l).toNat; have hd:mass l+(d:ℤ)=(4:ℕ):= by unfold d; omega
   obtain ⟨⟨i,p⟩,⟨j,q⟩,h₁⟩:= List.length_eq_two.mp hL
   let f:= paySlot F H K i j p q; let g:=paySlot F H K j i q p; let c:ℂ:=cross (parity i) (parity j); let u(t:ℝ):= f t+c*g t
   have hv(x:ℝ): bridgeG K F (enrol X G 0).symbol m (sail (ray l) x) = (x:ℂ)^2*u x:= by rw [ h₁,ray_go,List.map_cons,List.map_cons,List.map_nil ]; rw [branching hF hH]; dsimp only; rw [slot_pay,slot_pay]; unfold u f g c H; ring
   rw [ t_bud _ hd,torch_at ]; simp_rw [hv]; apply jet_two u ((pay_smooth (he.forms true).price hp H p q i j).add ( contDiff_const.mul ( pay_smooth (he.forms true).price hp H q p j i) )); simp [u,f,g,pay_stop (hu m)]; have hh:= mlength l; omega

lemma one_page (K:LineRule G)(X:Mob G)(V:Flats G) (n:ℕ)(z:ℂ): bridgePages K.half V (classicalPage X) n z = bridgeG K.half (V n z) X := by
   -- evaluate finsupp sum; permit zero value X
   unfold bridgePages
   have hv (k:ℕ)(T:Coat G): (classicalPage X).sum (fun i y=> Finsupp.single (i+k) (fun z => bridgeG K.half (T z) (y z))) = Finsupp.single k (fun z=>bridgeG K.half (T z) X):= by
       unfold classicalPage collapsed; rw [Finsupp.sum_single_index]; simp; simp [bridgeG_eq K.ok.rev, ← schedule]; rfl
   simp_rw [hv]; rw [Finsupp.sum_apply]; unfold Finsupp.sum; simp_rw [Finset.sum_apply]
   by_cases hn:n∈V.support; · rw [Finset.sum_eq_single_of_mem n hn,Finsupp.single_eq_same]; exact fun i _ h=>by simp [h]
   simp_rw [Finsupp.notMem_support_iff.mp hn]; rw [show bridgeG K.half ((0:Coat G) z) X= 0 from ?_]; exact Finset.sum_eq_zero fun i hi=> by rw [Finsupp.single_apply,if_neg (show i≠n from fun e=>hn (e ▸ hi))]; rfl
   simp [bridgeG_eq K.ok.rev, ← schedule]

theorem no_marked_here (K:LineRule G) (he:∀ (m:ℕ)(i j:Cfield G m), K.half m i j 0=0) (V:GraphSum G true 4)(hp:V.slots=2):
    (bridge K V (vertex (enrol X G 0))).instructions.pole=0 := by
    apply on_branch; intro n; unfold connect; simp only [factor, ↓reduceIte, Complex.ofReal_one,one_smul,Bool.false_eq_true, renorm_vertex]; obtain hv:= V.accepted
    filter_upwards [hv.after_rank n,(clockMoon hv.usable.clock n).mer.price] with z ht hu
    rw [one_page]; apply jetArm X K.ok he _ hu; change Goods V.slots _ at ht; rwa [hp] at ht
lemma branch_cursor (b:Bool) (V:GraphSum G true 4)(hp:V.slots=2): (bridge (cursor b) V (vertex (enrol X G 0))).instructions.pole=0:= by
    apply no_marked_here X (cursor b) _ V hp; simp [cursor,pickLine,A_zero]
end YM.MS.ScaleForest.Quadratic
