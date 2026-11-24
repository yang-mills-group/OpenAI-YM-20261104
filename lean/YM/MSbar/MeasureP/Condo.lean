import YM.MSbar.MeasureP.Thorn
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Lattice Gauge Push Uniform
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Whisk RG Precision Next.Free Exterior Laurent Bloch
open MultiNext.SignedSource Newt Debut Pattern Cane
variable {ι:Type}{G:Gauge}{c n:Side}{g:Ratio c n} {ρ : ℝ} {κ p:ℕ} {η a E D :ℝ}
variable (P : Cross g.count (TypeFace 1) (TypeFace 1))
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "X"=>pension g P G
local notation "L"=>(g.count.val:ℝ)
noncomputable def matry : List Axis → E4 →ℝ
| [],_=>1
| i::l,x=> (l.length+1:ℝ)⁻¹*x i*matry l (x-basis i)
lemma drama(k:ℕ)(f:Cover→ℝ)(x:E4): Newt.piece k f x= Yarn k (fun T=>matry T x*Newt.iterate f T 0):=by
    induction k generalizing x f with
    | zero=>rw [Newt.piece,Yarn,matry,one_mul];rfl
    | succ k ih=> rw [twilled,Newt.piece]; simp_rw [smul_eq_mul,Finset.mul_sum,ih]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [←mul_assoc,←sheen]; refine stitch k (fun m hm=>?_); rw [matry,hm,Newt.iterate]; ring
abbrev Strand (G:Gauge):= TypeFace 1 × G.ColorIndex
def argo (n:Side)(G:Gauge) (x:Site n)(s:Strand G):Primary n G:= ((x,s.1),s.2)
noncomputable def target (x i:Primary n G)(l:List Axis)(s:Strand G):= if (i.1.2,i.2)=s then matry l (xyz (voyage x i)) else 0
noncomputable def author (g:Ratio c n) (P:Cross g.count (TypeFace 1) (TypeFace 1)) (x:Primary n G) (l:List Axis)(s:Strand G)(j:Primary c G):=pension g P G l.reverse (argo n G x.1.1 s) j
variable (x i:Primary n G)(v:Primary c G)(h:Cane P D η a E κ p)
variable (t:ℕ)(ht:t≤κ)
include h ht
lemma theoret (l:List Axis)(hh:l.length=t) : Newt.iterate (lyrics g P x.1.1 i v) l 0 = pension g P G l.reverse (argo n G x.1.1 (i.1.2,i.2)) v:=by
    have he:=Debut.linear P x.1.1 i 0 (Pi.single v 1) l h.grid (fun s hv=> ⟨η,_,h.ηpos,h.res s (by omega)⟩)
    have hx (f:B→ℝ) : (∑ j:B, f j*(Pi.single v (1:ℝ): Positions B) j)=f v:=by simp [Pi.single_apply]
    rw [hx] at he -- maybe lhs under lambda
    simp_rw [show ∀ t:Cover,(∑ j:B, lyrics g P x.1.1 i j t*(Pi.single v 1:Positions B) j)=lyrics g P x.1.1 i v t from fun _=> hx _] at he
    simpa only [circle,argo,map_zero,zero_add] using he
lemma mailed : yarn g P x t i v= Yarn t (fun l=>∑ s:Strand G, target x i l s * author g P x l s v):=by
    unfold yarn; rw [drama]; refine stitch t fun l hl =>?_ ; rw [theoret P x i v h t ht l hl]; simp only [target, ite_mul]; simp [author]
local notation "Φ"=>treasure g G a p
lemma photo (l:List Axis)(s:Strand G) (hh:l.length=t) : (∑ j:B,treasure g G a p x j*|author g P x l s j|) ≤ (E*Real.exp η*(Fintype.card (TypeFace 1)*D))/L:=by
    have he:= crown g P (argo n G x.1.1 s) (h.res l.reverse (by simpa only [List.length_reverse,hh])) h.room h.a0 (zero_le_one.trans h.E0) h.sufficient
    rw [← mul_div_assoc,←mul_div_assoc] at he; have hq:0 ≤ E:=zero_le_one.trans h.E0; have hw:=h.D0
    apply he.trans; refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_; nth_rw 1 [←pow_one L]; exact pow_le_pow_right₀ (by exact_mod_cast g.count.property) (Nat.le_add_right ..)
end YM.MSbar.Measuring
