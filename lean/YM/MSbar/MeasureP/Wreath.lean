import YM.MSbar.MeasureP.Pins
import YM.MSbar.MeasureP.Shuttle
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Lattice Gauge Push Uniform
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Whisk RG Precision Next.Free Exterior Laurent Bloch
variable {ι:Type}{G:Gauge}{c n:Side}{g:Ratio c n} {ρ : ℝ} {κ p:ℕ} {η a E D :ℝ}
variable (P : Cross g.count (TypeFace 1) (TypeFace 1))
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "X"=>pension g P G
local notation "L"=>(g.count.val:ℝ)
open MultiNext.SignedSource Newt Debut Pattern
lemma pieceY [Fintype ι](f:ι→ Cover→ℝ)(w:ι→ℝ)(k:ℕ)(x:E4):Newt.piece k (fun z=>∑ b,f b z*w b) x=∑ b,Newt.piece k (f b) x*w b:=by
   induction k generalizing x f with
   | zero=>rfl
   | succ k ih=> simp only [Newt.piece]
                 simp_rw [show ∀ i:Axis,Newt.jump (fun z=>∑ b,f b z*w b) i=(fun z=>∑ b,Newt.jump (f b) i z*w b) from fun i=>by funext z; unfold Newt.jump; rw [←Finset.sum_sub_distrib]; simp_rw [sub_mul], ih]; simp only [smul_eq_mul]; simp_rw [Finset.mul_sum]; -- align triple
                 simp_rw [Finset.sum_mul]; rw [Finset.sum_comm (s:=Finset.univ (α:=ι))]; simp_rw [mul_assoc]
lemma tailY [Fintype ι](f:ι→ Cover→ℝ)(w:ι→ℝ)(k:ℕ)(x:Cover):Newt.tail k (fun z=>∑ b,f b z*w b) x=∑ b,Newt.tail k (f b) x*w b:=by
   unfold Newt.tail Newt.take; simp_rw [sub_mul,Finset.sum_sub_distrib,pieceY,Finset.sum_mul,Finset.sum_comm (s:=Finset.univ (α:=ι))]
lemma emblem [Fintype ι](f s:ι→ℝ)(hs:∀ i,0 ≤ s i)(t:ℝ)(h:∀ w:ι→ℝ,(∀ i, |w i| ≤ s i)→|∑ i,f i*w i|≤t) :(∑ i:ι,s i*|f i|) ≤ t:=by
    let w(i):= if 0≤f i then s i else -s i; apply le_trans (b:=|∑ i,f i*w i|) _ (h w (fun i=>by unfold w; split_ifs <;> simp only [abs_neg,abs_of_nonneg (hs i),le_refl]))
    apply le_trans _ (le_abs_self _); apply Finset.sum_le_sum; intro i _; unfold w; split_ifs with hv; simp [abs_of_nonneg hv,mul_comm]; simp [abs_of_neg (lt_of_not_ge hv),mul_comm]
structure Cane (P:Cross g.count (TypeFace 1) (TypeFace 1))(D η a E:ℝ)(k p:ℕ) :Prop where
   a0 : 0 ≤ a
   ηpos : 0 < η
   room : 4*a ≤ η
   D0 : 0 < D
   E0 : 1 ≤ E
   sufficient : ∀ x:ℝ,0≤x→(1+x)^p ≤ E*Real.exp (η/4*x)
   res (l:List Axis) (h:l.length≤k): (advanceC _ P l).strip η (D/(g.count.val:ℝ)^(1+l.length))
   grid : Odd g.count.val
namespace Cane
variable (x: Site n)(i:Primary n G)
local notation "J"=> lyrics g P x i
local notation "ϕ"=>grot g G a p
variable (h:Cane P D η a E κ p)(R :ℝ)(hr:0≤R) (z:Cover) {k:ℕ}(hk:k≤κ)
noncomputable def candle (a D η E R:ℝ)(p:ℕ):= factor a p (2*R)* (E*Real.exp η*(Fintype.card (TypeFace 1)*D))
local notation "Σ₀"=>candle a D η E R p
include h hk hr
lemma goodF: 0 ≤ candle a D η E R p:=by unfold candle factor; have hp:=h.D0; have hh:=h.E0; have hv:0≤E:=zero_le_one.trans hh; positivity
lemma billable (l:List Axis)(hk':l.length=k) (b:B→ℝ)(he:∀ v:B,|b v|≤grot g G a p x v)(hx:(size z:ℝ)≤ R*L) : ‖Newt.iterate (fun t:Cover=>∑ v:B, lyrics g P x i v t*b v) l z‖ ≤ candle a D η E R p / L^(1+k):=by
    rw [Debut.linear P x i z b l h.grid (fun s hv=> ⟨η,_,h.ηpos,h.res s (by omega)⟩)]
    let y:= Debut.circle x i z; let F:=factor a p (2*R)
    have hy : y.1.1=wrap n z+x:= rfl
    have hp (v:B): ϕ x v ≤ F*ϕ y.1.1 v:=by
       have he(v:B):2*(separation x (g.embed v.1.1):ℝ)/L≤2*R+2*separation y.1.1 (g.embed v.1.1)/L:=by
          have h0 :0<L:=by positivity
          have hD:separation x y.1.1 ≤ size z:=by rw [hy,separation_comm,separation,add_sub_cancel_right]; exact wrapped z n
          have hh:(separation x (g.embed v.1.1):ℝ) ≤ (size z:ℝ)+separation y.1.1 (g.embed v.1.1):=by exact_mod_cast (separation_triangle x y.1.1 (g.embed v.1.1)|>.trans (Nat.add_le_add_right hD _))
          apply sub_nonpos.mp; field_simp; nlinarith only [hh,hx]
       exact (inc p h.a0 (by positivity) (he v)).trans (bridge _ _ _ _ (by positivity) (by positivity))
    let f(v:B) := X l.reverse y v; have hf:0≤F:=by unfold F factor; positivity
    have hq:0 ≤ E:=zero_le_one.trans h.E0; have hR:=crown g P y (h.res l.reverse (by simpa only [List.length_reverse,hk'])) h.room h.a0 hq h.sufficient; rw [List.length_reverse,hk'] at hR
    refine (norm_sum_le ..).trans (le_trans (b:= F*∑ v:B,ϕ y.1.1 v*|f v|) ?_ ((mul_le_mul_of_nonneg_left hR hf).trans_eq ?_))
    · rw [Finset.mul_sum]; refine Finset.sum_le_sum fun v _=> ?_; simp only [norm_mul,Real.norm_eq_abs]; calc
         _ ≤ |f v| * (F*ϕ y.1.1 v):= mul_le_mul_of_nonneg_left ((he v).trans (hp v)) (abs_nonneg _)
         _ = _ := by ring
    unfold candle F; ring
lemma pieced (hx:R*L≥0) : (∑ v:B,grot g G a p x v * |Newt.piece k (lyrics g P x i v) (xyz z)|) ≤ ((4*((k:ℝ)+1))^k)*(1+(size z:ℝ))^k*(Σ₀/L^(1+k)):=by
    refine emblem _ _ (fun i=>grot_positive ..|>.le) _ (fun w hw=>?_); rw [←pieceY]; -- uses he∀ at 0
    have ht:0 ≤ Σ₀/L^(1+k):= div_nonneg (goodF P h R hr hk) (by positivity)
    exact component _ (fun t:Cover=>∑ b:B,J b t*w b) ht (fun l hl=> billable P x i h R hr 0 hk l hl w hw (by simpa only [show size (0:Cover)=0 from (by simp [size]),Nat.cast_zero])) z
lemma dressed (hx:(size z:ℝ) ≤ R*L): (∑ v:B,grot g G a p x v*|Newt.tail k (lyrics g P x i v) z|) ≤ Σ₀/L^(1+k)*(1+(size z:ℝ))^k:=by
    refine emblem _ _ (fun i=>grot_positive ..|>.le) _ (fun w hw=>?_); rw [← tailY]; exact localized k (div_nonneg (goodF P h R hr hk) (by positivity)) _ (fun l hl t ht=>billable P x i h R hr t hk l hl w hw ht) z hx
end Cane
end YM.MSbar.Measuring
