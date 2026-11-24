import YM.WilsonCoeffUV.Reclosure.Paths.SignedLift
/-!
# Signed rendering of any stacks; not the choice of representatives

Implicit length carried with whole channel on pulled links. All Arc
contour arities explicit. Averages exact as functions, and as coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near PowerSeries
open Stationary
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{k r t e:ℕ}{s a b v:ℝ}
variable {P Q : Ten ℝ (YForest G) r}

def huesT (P:Ten ℝ (YForest G) r): Ten ℝ (YForest G) r:= (Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, pendant s P
lemma huesT_plus (P Q:Ten ℝ (YForest G) r): huesT (P+Q)= huesT P+huesT Q:=by
   unfold huesT; have hz s: pendant s (P+Q)=pendant s P+pendant s Q:= by ext1 x; simp [pendant,mul_add]
   simp only [hz,Finset.sum_add_distrib,smul_add]
lemma huesT_mu (u:ℝ)(P:Ten ℝ (YForest G) r): huesT (u • P)= u • huesT P:=by
   unfold huesT; have hx s:pendant s (u • P)=u • pendant s P:= by ext1 x; simp [pendant]; ring
   simp_rw [hx, ← Finset.smul_sum]; rw [smul_comm]
lemma huesT_zero : huesT (0:Ten ℝ (YForest G) r)=0:=by simpa only [zero_smul] using huesT_mu 0 (0:Ten ℝ (YForest G) r)
lemma huesT_bill (he:0 ≤ s)(h:Amber Bank.terrain s a P): Amber Bank.terrain s (a*Real.exp (2*s)) (huesT P):=by
   let c:ℝ:= Fintype.card Signed; have hp: c>0:=by unfold c; positivity
   let A:=a*Real.exp (2*s)
   have hz:= (Amber.sum Finset.univ (fun i (_:i∈Finset.univ)=>gaze_paid i P h he)).smul c⁻¹
   apply hz.le; simp only [abs_of_nonneg (inv_nonneg.mpr hp.le),Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; change c⁻¹*(c*_ )≤_; rw [inv_mul_cancel_left₀ hp.ne']
lemma huesT_stroll (h:stroll P): stroll (huesT P):=by intro b x; simp only [huesT,Pi.smul_apply,Finset.sum_apply]; exact congr_arg (_ • ·) (Finset.sum_congr rfl fun i _=>gaze_stroll i P h b x)
lemma huesT_axis (s:Signed)(x:Fin r → YForest G) : huesT P (tickW s 0 ∘ x)=veil x s*huesT P x:=by
   have hx (w:Signed) : pendant (s*w) P (tickW s 0 ∘ x)= veil x s* pendant w P x:=by
      obtain ⟨x,rfl⟩:=(Equiv.piCongrRight (fun _ : Fin r=> pendants (G:=G) w)).surjective x
      change pendant (s*w) P (tickW s 0 ∘ tickW w 0 ∘ x)= veil (tickW w 0 ∘ x) s*pendant w P (tickW w 0 ∘ x); rw [pendant_at w];
      rw [show tickW s 0 ∘ tickW w 0 ∘ x=tickW (s*w) 0 ∘ x from funext fun i=> axial ..,pendant_at, veil_axial]; ring
   simp only [huesT, Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [mul_left_comm (veil x s)]; congr 1
   rw [Finset.mul_sum]
   rw [← Equiv.sum_comp (Equiv.mulLeft s)]; exact Finset.sum_congr rfl fun i _=> hx i
lemma huesT_sym (p:stroll P)(s:Signed)(x:Fin r →YForest G)(z:Cover): huesT P (tickW s z ∘ x) = veil x s * huesT P x:=by
   rw [show tickW s z ∘ x=jog z ∘ tickW s 0 ∘ x from ?_, huesT_stroll p, huesT_axis]
   funext i; simp only [Function.comp_apply]; obtain ⟨⟨x,i⟩,j,h⟩:= every_stone (x i); rw [← h,color_shove,color_shove]; refine Prod.ext ?_ rfl; unfold stone jog; simp; abel
lemma pendant_same (s:Signed)(h:∀ x,P (tickW s 0 ∘ x)= veil x s*P x): pendant s P=P:=by
   funext x; obtain ⟨x,rfl⟩:=(Equiv.piCongrRight (fun _ : Fin r=> pendants (G:=G) s)).surjective x; exact (pendant_at s P x).trans (h x).symm
lemma huesT_same (h:∀ s x,P (tickW s 0 ∘ x)= veil x s *P x): huesT P=P:=by
   let c:ℝ:= Fintype.card Signed; have hp:c>0:=by unfold c; positivity
   have he s:= pendant_same s (h s)
   simp only [huesT,he,Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R:=ℝ), Finset.card_univ]; rw [inv_smul_smul₀ hp.ne']

lemma rye_mu (b:ℝ)(F:Link G c→ℝ)(h:Green F)(r:ℕ): rye (b • F) r=b • rye F r:=by
   funext x; simp only [rye,iteratedFDeriv_const_smul_apply (h.of_le (by simp)),_root_.smul_apply]; rw [smul_comm]; rfl
lemma rye_plus (F W: Link G c→ℝ)(h:Green F)(p:Green W)(r:ℕ): rye (F+W) r=rye F r+rye W r:=by
   funext x; simp only [rye, iteratedFDeriv_add_apply (h.of_le (by simp)) (p.of_le (by simp)),_root_.add_apply, smul_add]; rfl
lemma rye_scoped {I:Type*} {S:Finset I} {W:I→Link G c→ℝ}(p:∀ i∈S, Green (W i))(r:ℕ):
   rye (∑ i∈S, W i) r= ∑ i∈S, rye (W i) r :=by
    have he: Green (∑ i∈S,W i):=by unfold Green; rw [show (∑ i∈S,W i)=fun x=>∑ i∈S,W i x from funext fun x=>Finset.sum_apply ..]; apply ContDiffAt.sum; exact p
    apply unique_kernel (rye_sym he _) (Blue.Smooth.sum (fun i t=>rye_sym (p i t) _))
    rw [←jet_apply, jet_sum S W p,map_sum,map_sum]; simp only [jet_apply]
lemma hue_roll {F: Config G c→ℝ}(h:Green (F ∘ input G c))(f:post G t)(v:Amber Bank.terrain s a f)(p:0<s)(hp:stroll f)
   (he:rye (F ∘ input G c) (t+1)=lagoon f c):
   rye (fun x=>Patch.average fun u:Signed=>F (pull u 0 (input G c x))) (t+1) = lagoon (huesT f) c :=by
    let T (u:Signed) (x:Link G c):= F (pull u 0 (input G c x))
    have hx u : T u = fun x=> (F ∘ input G c) (markSign G u 0*ᵥ x):= by funext x; simp_rw [T,Function.comp_apply,mantle_input,sign_turn]
    let d:ℝ:=(Fintype.card Signed:ℝ)⁻¹
    have hh u : Green (T u) := by rw [hx]; apply ContDiffAt.comp (g:=F ∘ input G c) _ _ (board _); simp; exact h
    have hz u: rye (T u) (t+1)=lagoon (pendant u f) c:=by
        rw [wraps_pendant u f hp c, ← he,hx]; have he:=congr_fun (beam (markSign G u (0:Site c)) (F ∘ input G c) h (t+1)) (t+1)
        simp_rw [sprig,Nat.add_zero] at he; rwa [shine_lit] at he
    rw [show (fun x=>Patch.average fun u:Signed=> F (pull u 0 (input G c x)))=d • ∑ u:Signed, T u from funext (fun x=> by simp only [Pi.smul_apply,Finset.sum_apply]; rfl)]
    have hU : Green (∑ u: Signed,T u) := by unfold Green; rw [show (∑ u:Signed,T u)=fun x=>∑ i:Signed,T i x from funext fun x=> Finset.sum_apply ..]; apply ContDiffAt.sum; exact fun _ _=>hh _
    rw [rye_mu _ _ hU,rye_scoped (fun i _=>hh i),huesT, lagoon_scalar,lagoon_join _ (fun i _=>⟨_,gaze_paid i f v p.le⟩) p]; simp_rw [hz]; rfl

-- finite and cover signed orbit wrap

def surf (P: PrismA G)(n:Side): PChart G n:= fun k=> if P.grade≤ k then
    sprig (turnSeries P.cells (m:=n)) (P.rise+2) (k-P.grade) else 0

def sands (P:SeriesA G)(n:Side): PChart G n:= (P.map fun x=>surf x n).sum
lemma stands_self (h:0<s)(p:PrismA G)(g:Commission p.cells s a p.grade)(e t:ℕ)(n:Side):
   surf p n e (t+1)= lagoon (huesT (recordV p e (t+1))) n :=by
    unfold surf recordV chess; split; swap; · symm; change lagoon (huesT (0 : post G t)) n=0; rw [huesT_zero, lagoon_none]
    set j:= e-p.grade; by_cases H:p.rise+2+j=t+1; swap
    · rw [sprig,shine_dark H,huesT_same (P:=_)]; swap; · rw [fire,shine_dark H]; simp
      rw [fire,shine_dark H,lagoon_none]
    have he:= paid_packet h g.toll (by omega) j (t+1)
    rw [sprig,H,shine_lit]; apply hue_roll (score_analytic n p.cells h g.toll).contDiffAt _ (cap_pay h g.toll (by omega) j (t+1)) (div_pos h (by norm_num)) he.road
    change rye (seriesScore n p.cells) _=_; have hx:=wraps_fire h g.toll n j t; unfold written sprig at hx; rwa [H,shine_lit] at hx
lemma sands_zero_v (P:SeriesA G)(v n): sands P n v 0=0:=by
    induction P with
    | nil=>rfl
    | cons i P ih=>
      rw [show sands (i::P) n=surf i n+sands P n from rfl, Pi.add_apply,Pi.add_apply,ih,add_zero]
      unfold surf; split; · unfold sprig; rw [shine_dark (by omega)]
      rfl
theorem wraps_signed (h:0<s)(P: SeriesA G)(g:Draw P s a) (e t:ℕ)(n:Side):
   sands P n e (t+1)= lagoon (huesT (murals P e (t+1))) n:=by
    induction P with
    | nil=> symm; change lagoon (huesT (0:post G t)) n=0; rw [huesT_zero,lagoon_none]
    | cons i P ih=>
      have hp:=g.2 i (List.mem_cons_self ..); have ht:Draw P s a:= ⟨g.1,fun k p=>g.2 _ (List.mem_cons_of_mem _ p)⟩
      have hT:0<steep s:=div_pos h (by norm_num)
      rw [show sands (i::P) n=surf i n+sands P n from rfl, murals_cons]; simp only [Pi.add_apply, stands_self h i hp,ih ht,huesT_plus]
      rw [lagoon_plus (huesT_bill hT.le (pollen i hp h e _)) (huesT_bill hT.le (pollen_sum h ht e (t+1))) hT hT]

end YM.WilsonCoeffUV.Bank.Mosaic
