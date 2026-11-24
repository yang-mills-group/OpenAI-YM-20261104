import YM.MS.Local.Curls
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Coh
/-!
# A-only slots are curls of polynomial slots

Keep endpoint derivative charge. Spanned by ordinary elementary curvature jets
($ip f$ in our wave convention) per color. No color averaging until done.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor MatrixLet
open Landau Detect Detect.Mark Radial Submodule
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {h : ℤ} {f : Grade G} {r : ℕ}


def gpath (u v:Axis) (c:CI G) (m:FourP→ℂ) : Grade G := fun a=> match a with
| (((some i,false),b),p)=> if b=c then m p*( I*(p u:ℂ)*(if i=v then 1 else 0)-I*(p v:ℂ)*(if i=u then 1 else 0)) else 0
| _=>0
lemma gps (u v:Axis) (i :CI G) (m:FourP→ℂ) (hx: Plane.Shape m (h-2)) : Horizontal (gpath u v i m) h:= by
   have hv : gpath u v i m∈ yields h 0:= by
      refine seedStar.mpr ⟨fun k=>?_, fun i h'=>?_⟩; swap
      · rcases i with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> norm_num [ghostNo,ghostChannel,gpath] at h' <;> rfl
      rcases k with ⟨⟨_|k,_|_⟩,c⟩ <;> first | exact form_zero _| skip
      by_cases hj:c=i; swap; · simp only [gpath,hj,↓reduceIte]; exact form_zero _
      let f (i:Axis) p := ((p:FourP) i:ℂ)
      have heq i : Plane.Shape (f i) 1:= by simpa [f] using Shape.scalar_pow 1 (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Axis=> ℝ) i)
      let r (a:Axis):ℂ:= if k=a then 1 else 0
      let R:=((I*r v) • f u)+ ((-(I*r u)) • f v); have hR : Plane.Shape R 1:= ((heq u).scalar _).add ((heq v).scalar _)
      convert! hx.mul hR using 1; · ext; simp only [gpath,hj,↓reduceIte,R,r,f,Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
      unfold mslug; norm_num [ghostNo,wfield,ghostChannel,dim]; omega
   refine ⟨hv,?_⟩; have hs := stays _ _ _ hv
   ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> first | (solve | refine (seedStar.mp hs).real' _ ?_; norm_num [ghostNo,ghostChannel])| skip
   change Q _ (C c p)=0; rw [movesC]; by_cases hp:c=i <;> simp [gpath,mul_ite,hp,mul_sub] ; ring

lemma across (H : Horizontal f h) (c:CI G) (p : FourP) : ∑ i:Axis,(p i:ℂ)*f (W i c p)=0:= by
   have he:= movesC f c p; rw [H.2] at he; simp_rw [mul_assoc,← Finset.mul_sum] at he; exact (mul_eq_zero.mp he.symm).resolve_left Complex.I_ne_zero

lemma oriented (H: Horizontal f h): f∈ Submodule.span ℂ {g:Grade G| ∃ u v i,∃ p:FourP→ℂ,  Plane.Shape p (h-2) ∧ g=gpath u v i p} := by
    let P:=Submodule.span ℂ {g:Grade G| ∃ u v i,∃ p:FourP→ℂ,  Plane.Shape p (h-2) ∧ g=gpath u v i p}
    let F (c:CI G) i x:= f (W i c x)
    have hf i c : Plane.Shape (F c i) (h-1):= ((seedStar.mp H.1).form (gauge i,c))
    rcases lt_or_ge h 1 with h1|h1
    · have he : f=0 := by
         ext i; by_contra! he
         obtain ⟨j,c,p,rfl⟩:= Tall_l H i he
         exact he (congr_fun ((hf j c).charge (by omega)) _)
      rw [he]; exact P.zero_mem
    let T (a b :Axis) (c:CI G) := gpath a b c (square a (F c b))
    have hT (a b:Axis) (c:CI G) : T a b c ∈ P:= by
       have hR : Plane.Shape (square a (F c b)) (h-2):= by convert shape_der (hf b c) (spike a) using 1; rfl; omega
       exact Submodule.subset_span (mem_setOf.mpr ⟨a,b,c,_,hR,rfl⟩)
    -- sum_{ab} T : value at vector i = i p_a square a F_i - i p_b square i F_b
    let L := ∑ c:CI G,∑ a:Axis,∑ b:Axis,T a b c
    have hv : (I*(h:ℂ)) • f=L:= by
       let F' := (I*(h:ℂ)) • f
       ext ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩
       all_goals simp only [Pi.smul_apply,L,Finset.sum_apply]
       all_goals first | (solve | rw [(seedStar.mp H.1).real' _ (by norm_num [ghostNo,ghostChannel])]; simp [T,gpath]) | skip
       simp [T,gpath,mul_ite,mul_sub]
       let z x := (p x:ℂ)*(square x (F c i) p - square i (F c x) p)
       have hm x : square x (F c i) p*(I*(p x:ℂ))-square i (F c x) p*(I*(p x:ℂ))=I*z x:= by unfold z; ring
       rw [← Finset.sum_sub_distrib]; simp_rw [hm,← Finset.mul_sum]
       have hk:= Radial.curl (fun x=>hf x c) (across H c) p i; change (_*F c i p) = ∑ x,z x at hk; rw [← hk]; push_cast; change I * _ * F c i p= _; ring
    have hR : I*(h:ℂ) ≠ 0:= mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr (by omega))
    rw [← inv_smul_smul₀ hR f,hv]
    exact P.smul_mem _ (sum_mem fun j _=> sum_mem fun i _=> sum_mem fun a _=> hT i a j)
end YM.MS.Local.BV
