import YM.OPE.Measuring.Charts

/-!
# Wedge test to a bound on a Narrow tree scale chart

`whole` is the engineering factor multiplying each leaf by the dimension
power at its *own parent's* scale. The plotted result `signal` here is just a
test rescaling of the SAME quantity (node size doesn't dilute the fields or
replace their actual fixed normalization). Removes the slacks in a power
rate when there is a smooth extension to the total equal-position diagonal
of the finite plotted quantity `g` near every copy of the origin point. E.g.
for `Narrow` such extensions here for coefficients and their composition do
not require any positive lower bound on separations inside the (Fork f). No claim
of the premise without the regular-germ proof (not automatic at true
multifield collisions). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Tree
open Orbits Orbits.Reader Prescription Nesting Nesting.Tree Function Filter Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n:ℕ}{f:Fin n→Tree}
local notation "tree" => Fork f
set_option quotPrecheck false
local notation "Ind" => Nonroot f
local notation "box" => (Ind→ℝ) × (Fork f).Plot
variable {B:Type*}[NormedAddCommGroup B][NormedSpace ℝ B]

def entrance (d:Bool)(D:(Fork f).Inner→ℕ):ℕ:=if d then ∏ v:Ind,(D (Sum.inr v)+1) else 0
def pace (d:Bool)(D:(Fork f).Inner→ℕ)(v:Ind):ℕ:=entrance d D / (D (Sum.inr v)+1)
def allowance (d:Bool)(D:(Fork f).Inner→ℕ)(r:(Fork f).Inner→ℝ):ℝ := if d then ∑j:Ind,(r (.inr j))^(D (.inr j)+1) else 1
variable (d:Bool)(w:(Fork f).Leaf→ℕ)(m:ℝ)(D:(Fork f).Inner→ℕ)
local notation "powerT" => parametrise (pace d D)
lemma pace_mul (hd:d=true)(j:Ind): pace d D j * (D (.inr j)+1)=entrance d D:=by rw [pace,Nat.div_mul_cancel (by simp only [entrance,hd,if_true]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _))]
lemma pace_pos (hd:d=true)(j:Ind): 0<pace d D j := by
     have he:=pace_mul d D hd j; have hh:=Finset.prod_pos (f:=fun j:Ind=> D (Sum.inr j)+1) (s:=Finset.univ) fun i _=> Nat.succ_pos ..; apply Nat.pos_of_ne_zero fun h=>?_ ; apply Nat.ne_of_lt hh
     rw [h,zero_mul,entrance,if_pos hd] at he; exact he

private lemma whole_ref {r:(Fork f).Inner→ℝ}(hr:∀ i, 0 < r i) {δ:ℝ}:whole tree w ((Fork f).ratios 1 r)*toll (fun j=> (w j:ℝ)) δ m r = (r (Sum.inl ()))^(m-δ) * ∏ j:Ind,((Fork f).ratios 1 r (Sum.inr j))^(-δ):=by
     let T:=(Fork f).ratios 1 r
     rw [← toll_eq (w:=fun j=>(w j:ℝ)) (hr (Sum.inl ()))]; change whole tree w T*(_ * ∏ v:(Fork f).Inner,(T v)^(-((Fork f).headSum _ v)-δ))= r (.inl ())^(m-δ) * ∏ j:Ind,(T (.inr j))^(-δ)
     have hP: ∀ q:(Fork f).Inner,0<T q:=whole_offset.ratio_pos (show 0<(1:ℝ) from one_pos) hr
     have hh : ∏ v:(Fork f).Inner,(T v)^( (-((Fork f).headSum (fun j=>(w j:ℝ)) v) -δ)) = (∏ v:(Fork f).Inner, (T v)^((-((Fork f).headSum (fun j=>(w j:ℝ)) v)-(0:ℝ)))) * (∏ v:(Fork f).Inner,(T v)^(-δ)):= by
         rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl (fun x _=> ?_); rw [← Real.rpow_add (hP x)]; apply congr_arg (_^·) (?_); ring
     have hv: whole tree w T* ((r (Sum.inl ())) ^ m * ∏ v : (Fork f).Inner, (T v) ^ ((-(Fork f).headSum (fun j=> (w j:ℝ)) v - (0:ℝ)))) = (r (Sum.inl ())) ^ m := by change whole tree w T*scaleFee _ r 0 m= r (Sum.inl ())^m; rw [toll_eq (hr (Sum.inl ()))]; exact whole_offset (u:=w) m hr
     have he: (∏ v:(Fork f).Inner,(T v)^(-δ))=r (.inl ())^(-δ)*∏ j:Ind,(T (.inr j))^(-δ):=by rw [prod_inner, Fintype.prod_sigma]; apply congr_arg (·*_) (congr_arg (·^(-δ)) (div_one _))
     rw [hh,← mul_assoc (r (Sum.inl ())^m),← mul_assoc, hv,he,← mul_assoc,← Real.rpow_add (hr _)]; rfl

private lemma main_parameters {x y:ℝ}{q:Ind→ℝ}(M:ℝ)(h:0<x)(hx:x≤1)(hy:0<y)(he:y≤1)(hq:∀j,q j∈Ioc (0:ℝ) 1):∀ v:(Fork f).Inner,powerT x y q v∈Ioc (0:ℝ) 1:=fun v=>by cases v with
  | inl=>exact ⟨h,hx⟩
  | inr j=> exact ⟨mul_pos (pow_pos hy _) (hq ..).1, mul_le_one₀ (pow_le_one₀ hy.le he) (le_of_lt (hq j).1) (hq j).2⟩

private lemma penalty {y:ℝ}{q:Ind→ℝ}(x:ℝ)(hy:0<y)(hq:∀j,q j∈Ioc (0:ℝ) 1):allowance d D (powerT x y q) ≤ (1+(Fintype.card Ind:ℝ))*y^(entrance d D):=by
    unfold allowance; split_ifs with hd
    · apply (Finset.sum_le_sum (s:=Finset.univ) (g:=fun i:Ind=>(1:ℝ)*y^(entrance d D)) (fun i _=>?_)).trans ?_
      · rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      change ((y ^ (pace d D i) * q i)^(D (Sum.inr i)+1))≤ _; rw [mul_pow,← pow_mul,pace_mul d D hd]; rw [one_mul]; exact mul_le_of_le_one_right (pow_nonneg hy.le _) (pow_le_one₀ (hq _).1.le (hq _).2)
    rw [entrance,if_neg hd,pow_zero,mul_one]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)

variable (g:(Fork f).Plot→B)
def signal (p:ℝ×ℝ× box):B:=(whole tree w (powerT p.1 p.2.1 p.2.2.1)) • g (model tree 1 (powerT p.1 p.2.1 p.2.2.1) p.2.2.2)

variable (M':ℝ)
local notation "panel" => Icc (0:(Ind→ℝ)) 1 ×ˢ (Metric.closedBall (0:(Fork f).Plot) (max M' 1))
variable (ht:Narrow (Fork f)) (hG:∀ x:E4,∀ᶠ z in 𝓝 (fun _:(Fork f).Positions=>x),ContDiffAt ℝ ∞ g z)
include hG in
lemma signal_ready (x:ℝ)(y:box)(hy:y.1≥0): ∀ᶠ z in 𝓝 ((0:ℝ),x,y), ContDiffAt ℝ ∞ (signal d w D g) z := by
     let p(z:ℝ×ℝ×box):=powerT z.1 z.2.1 z.2.2.1
     let F(z:ℝ×ℝ×box):=model tree 1 (p z) z.2.2.2
     let P(z:ℝ×ℝ×box):=whole tree w (p z)
     have hpi(i:(Fork f).Inner):ContDiff ℝ ∞ (fun z=>p z i):=contDiff_pi.mp (parametrise_smooth contDiff_fst (contDiff_fst.comp contDiff_snd) (fun i=> (contDiff_apply ℝ ℝ i).comp (by fun_prop))) i
     have hP:ContDiff ℝ ∞ P := contDiff_prod (t:=Finset.univ) (fun i hi=>(hpi i).pow _)
     have hθ: ContDiff ℝ ∞ F:=model_smooth tree contDiff_const hpi (fun i=> (contDiff_apply ℝ E4 i).comp (by fun_prop))
     have hQ:F (0,x,y)=fun _=>y.2 (.inl ()):=(by unfold F p; change model _ _ (powerT 0 x y.1) y.2= _; rw [parametrise_zero (f:=f) y.1 0, model_base]; simp)
     have hv:=hθ.continuous.continuousAt.tendsto.eventually (f:=F) (l₁:=𝓝 ((0:ℝ),x,y)) (l₂:=𝓝 (F (0,x,y))) (p:=fun z=> ContDiffAt ℝ ∞ g z) (by rw [hQ]; apply hG)
     exact hv.mono (fun i hi=>(hP.contDiffAt.smul (hi.comp i hθ.contDiffAt)))

private lemma boot_range (x:ℝ)(b:box) {y:ℝ}(F:ℝ) (hp:∀ j,0<(b.1 j))(hy:0<y): (∏ i:Ind,(powerT x y b.1 (Sum.inr i))^F) = y^(F* (∑ i:Ind, pace d D i:ℝ)) * ∏ i:Ind,(b.1 i)^F :=by
      have he(i:Ind): powerT x y b.1 (Sum.inr i)=y^(pace d D i) * b.1 i :=rfl
      simp_rw [he]
      have hw(i:Ind): (y^(pace d D i) * b.1 i)^F = y^((pace d D i:ℝ)*F)*(b.1 i)^F:= by rw [Real.rpow_natCast_mul hy.le,Real.mul_rpow (pow_nonneg hy.le _) (hp _).le]
      rw [Finset.prod_congr rfl (fun i (_:i∈(Finset.univ:Finset Ind))=>hw i),Finset.prod_mul_distrib]; congr 1; rw [mul_comm F,Finset.sum_mul]
      apply Eq.symm (Real.rpow_sum_of_pos hy ..)

variable (h0 : ∀ μ:ℝ,0≤μ→∀ ε>0,∀ᶠ x:ℝ in 𝓝[>]0,∀s:(Fork f).Inner→ℝ,∀ z:(Fork f).Plot, Accept x μ 1 s z → ‖g z‖ ≤ (toll (fun i=>(w i:ℝ)) ε m s) * allowance d D ((Fork f).ratios 1 s))

include ht h0
private lemma wire (ε:ℝ)(hε:0<ε):∃ c:box→ℝ, ∀ᶠ x:ℝ in 𝓝[>]0, ∀ y:ℝ,0<y→ y≤1→∀ b:box, (b∈panel ∧ (∀ j,0<b.1 j)) → ‖signal d w D g (x,y,b)‖ ≤ c b * x^(m-ε)*y^((entrance d D:ℝ)-ε):=by
     let M : ℝ:=max M' 1
     have hμ : 0≤M := le_trans zero_le_one (le_max_right ..)
     obtain ⟨μ,hμ',hg⟩:=nice ht hμ
     let W:ℝ:= ∑ i:Ind,(pace d D i:ℝ); let c:ℝ:= 1+Fintype.card Ind
     have hW : 0≤W:=Finset.sum_nonneg fun _ _=>Nat.cast_nonneg _
     let η:=ε/(1+W)
     have he: 0<η:= by unfold η; positivity
     have he₁: η≤ε:= div_le_self hε.le (le_add_of_nonneg_right hW)
     have he₂: η*W≤ε:=by unfold η; calc _ ≤ ε/(1+W)*(1+W):=by gcongr; linarith
                                       _ = ε:= div_mul_cancel₀ ε (by linarith)
     refine ⟨fun b=>(1+(Fintype.card Ind:ℝ))*∏ j:Ind,(b.1 j)^(-η),?_⟩
     filter_upwards [h0 μ (hμ.trans hμ') η he,self_mem_nhdsWithin (s:=Ioi (0:ℝ)), eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (zero_lt_one' ℝ))] with x hx hX h' y hy hy' b hb
     let p:=powerT x y b.1; let s:= sizes tree 1 p; let z:=model tree 1 p b.2
     have hp:= (show ∀i,p i ∈ Ioc (0:ℝ) 1 from main_parameters d D μ hX h' hy hy' (fun i=>⟨hb.2 i,(hb.1.1.2 i)⟩))
     have hs: Tapered tree 1 1 s:= sizes_good (show 0<(1:ℝ) from one_pos) hp
     have hv: s (Sum.inl ())=x := one_mul ..
     have hZ : ‖b.2‖≤M:= by rcases hb with ⟨⟨ha,hc⟩,ho⟩; simpa only [Metric.mem_closedBall,dist_zero_right] using hc
     have hΓ: Immediate M 1 tree s z:=on_model tree _ ht hp (zero_lt_one' ℝ) hμ (fun j=> (((norm_le_pi_norm b.2 j).trans hZ)))
     have hS:= sizes_ratios (u:=p) (t:=Fork f) one_ne_zero (fun j=>(hp j).1.ne') -- p in sizes_ratios is real, fix
     have hz:= hx s z (show Accept x μ 1 s z from ⟨⟨hs.positive _,hv.le,hs.2.2⟩,hg hs hΓ,hv⟩)
     have hNorm: ‖signal d w D g (x,y,b)‖ = whole tree w p * ‖g z‖:= by
           change ‖whole tree w p • g z‖ = _; rw [norm_smul,Real.norm_of_nonneg (whole_good tree (fun j=>(hp j).1)|>.le)]
     rw [← hS] at hNorm
     rw [hNorm]; refine le_trans (mul_le_mul_of_nonneg_left hz (whole_good tree (fun j=>(whole_offset.ratio_pos one_pos (fun j=>hs.positive j) j)) |>.le)) (?_)
     change (Fork f).ratios 1 s = p at hS
     rw [← mul_assoc,whole_ref w m (fun j=>hs.positive j),hS,hv]
     have hBoot:∏ i:Ind,p (.inr i)^(-η) = y^((-η)*W)*∏i:Ind,(b.1 i)^(-η):= by exact boot_range d D x b (-η) (by exact hb.2) hy
     change _ * (∏ i:Ind,p (.inr i)^(-η)) * _ ≤ _
     rw [hBoot]
     have h' := penalty d D (q:=b.1) x hy (fun i=>⟨hb.2 i,(hb.1.1.2 i)⟩)
     change 0<x at hX
     have hPi:0 ≤ ∏i:Ind,(b.1 i)^(-η):=Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (hb.2 i).le _)
     refine le_trans (mul_le_mul_of_nonneg_left h' (show 0 ≤ x^((m:ℝ)-η)*(y^((-η)*W) * ∏i:Ind,(b.1 i)^(-η)) from by positivity)) (?_)
     let A:=∏ i:Ind,(b.1 i)^(-η); let e':ℝ:= entrance d D
     change x^((m:ℝ)-η) * (y^((-η)*W)*A) * (c*y^(entrance d D)) ≤ _
     calc _ = c*A * x^((m:ℝ)-η) * y^(e'-η*W):=by rw [Real.rpow_sub hy]; change _= _ * _ * ((y^(entrance d D:ℝ) * (y^(η*W))⁻¹)); rw [Real.rpow_natCast,neg_mul,Real.rpow_neg hy.le]; ring
             _ ≤ c*A*x^(m-ε)*y^(e'-ε):=by
                 refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hX (by assumption) (by linarith only [he₁])) (show 0≤c*A from ?_)) (Real.rpow_le_rpow_of_exponent_ge hy hy' (by linarith only [he₂])) (Real.rpow_nonneg hy.le _) (?_)
                 · unfold c A; positivity
                 exact mul_nonneg (mul_nonneg (by unfold c; positivity) hPi) (Real.rpow_nonneg hX.le _)

omit h0
include hG
lemma wedge_price {m:ℕ}(h0 : ∀ μ:ℝ,0≤μ→∀ ε>0,∀ᶠ x:ℝ in 𝓝[>]0,∀s:(Fork f).Inner→ℝ,∀ z:(Fork f).Plot, Accept x μ 1 s z → ‖g z‖ ≤ (toll (fun i=>(w i:ℝ)) ε (m:ℝ) s) * allowance d D ((Fork f).ratios 1 s)):
    ∃ C:ℝ, ∀ᶠ x:ℝ in 𝓝[>]0, ∀y:ℝ,0<y→y≤1→∀ b:box, b∈panel∧(∀ j,0<b.1 j) →
       ‖signal d w D g (x,y,b)‖ ≤ C*x^(m:ℕ)*y^(entrance d D):=
          Axes.strong_grid (S:=panel) (n:=m) (e:=entrance d D) ({b:box| b∈panel∧∀j,0<b.1 j}) (isCompact_Icc.prod (isCompact_closedBall ..)) (fun _ h=>h.1) (fun y _ u hu=>signal_ready d w D g hG y u hu.1.1) (fun ε hε=>wire d w (m:ℝ) D g M' ht h0 ε hε) -- include hG?

omit hG ht
lemma rent {x:ℝ}{u:(Fork f).Inner→ℝ} (hx:0 < x)(h:u (.inl ())=x)(h_u:∀i:Ind,u (.inr i)∈Ioc (0:ℝ) 1)(hn:d=true→Nonempty Ind): ∃ y∈Ioc (0:ℝ) 1,∃ q:Ind→ℝ, (∀ v,q v∈Ioc (0:ℝ) 1) ∧ u=parametrise (pace d D) x y q ∧ y^(entrance d D) ≤ allowance d D u :=by
    by_cases hd:d=true
    swap
    · let v:Ind→ℝ:=u ∘ Sum.inr
      refine ⟨1,⟨zero_lt_one,le_rfl⟩,v,h_u,(funext fun k=>(?_)),?_⟩
      · rcases k with ⟨⟩|k; exact h; exact (by rw [parametrise,one_pow,one_mul]; rfl)
      exact (show (_:ℝ) ≤ 1 by simp).trans_eq (Eq.symm (if_neg hd) : 1=allowance d D u)
    haveI:Nonempty Ind:=hn hd
    let W:=pace d D; have hw:= pace_pos d D hd
    let y0(j:Ind):ℝ:= (u (Sum.inr j))^((W j:ℝ)⁻¹)
    obtain ⟨j,hj⟩:=Finite.exists_max y0
    let y:=y0 j; let q(p:Ind):= u (Sum.inr p)/y^(W p)
    have hy:0 < y:=Real.rpow_pos_of_pos (h_u j|>.1) _
    have hy':y ≤ 1:=Real.rpow_le_one (h_u j).1.le (h_u j).2 (inv_nonneg.mpr (Nat.cast_nonneg _))
    have he(i):y0 i ^ W i = u (Sum.inr i):=Real.rpow_inv_natCast_pow ((h_u i).1.le) ((hw i).ne')
    have hq(i):q i∈Ioc (0:ℝ) 1:=⟨div_pos (h_u i).1 (pow_pos hy _), (div_le_one (pow_pos hy _)).2 (by rw [← he]; exact pow_le_pow_left₀ (Real.rpow_nonneg ((h_u i).1.le) _) (hj i) _)⟩
    refine ⟨y,⟨hy,hy'⟩,q,hq,?_ ,?_⟩
    · funext k; cases k with
      | inl v=> cases v; exact h
      | inr i=> exact (show y^(W i)*q i = _ from mul_div_cancel₀ (u (.inr i)) (pow_ne_zero _ hy.ne')).symm
    change y^_ ≤ allowance d D u
    rw [← pace_mul d D hd j,pow_mul,show (y^(pace d D j))=u (Sum.inr j) from he j]
    unfold allowance; rw [if_pos hd]; refine Finset.single_le_sum (f:=fun i=>(u (Sum.inr i))^(D (Sum.inr i)+1)) (fun i _=> pow_nonneg ((h_u i).1.le) _) (Finset.mem_univ _)

end YM.OPE.Measuring.Tree
