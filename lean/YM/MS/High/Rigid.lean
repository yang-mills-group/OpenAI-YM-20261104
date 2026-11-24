import YM.MS.High.Slice
/-!
# Symmetries of momentum-dilation test (`skin`). Hold rankwise/masked.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color
open scoped Topology ContDiff
variable {G : Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
   {F : Law G} {M : Reading G} {r : ℕ} {b : Bool} {w : List (Lane4 G)}
-- Only case where momentum-space observation on reciprocal net.
omit [NormedSpace ℝ E] in
@[simp] lemma invert_sail (w : List (Lane4 G)) (p:ℝ) : sail (ray (invertMom w)) p=invertMom (sail (ray w) p):=by simp [ray_go,invertMom,Function.comp_def]
@[simp] lemma ray_sail_sign (s:Signed) (w : List (Lane4 G)) (p:ℝ) : sail (ray (w.map (permute s))) p=(sail (ray w) p).map (permute s):= by
   have he (v: FourP): s.act (p • v) = p • s.act v := by
       ext x; unfold Signed.act; simp only [Pi.smul_apply]; split <;> first | rfl | simp
   simp [ray_go,permute, Function.comp_def, he]
@[simp] lemma sign_const (s:Signed) (w : List (Lane4 G)) (p:ℝ): (sail (ray w) p).map (negateField s)= w.map (negateField s):= by simp only [ray_go,List.map_map]; rfl
lemma sign_course (s:Signed) (hw:Course b w): Course b (w.map (permute s)):= by
   intro h; suffices hp : ∀ (u:List (Lane4 G)), net (u.map (permute s)) = s.act (net u) by rw [hp,hw h,Signed.act_zero]
   intro u; induction u with
   | nil=> simp [net]
   | cons i w ih=> simp [ih,permute]
lemma sign_dim (s:Signed) (w : List (Lane4 G)): fieldDim wfield (w.map (permute s))=fieldDim wfield w:= by simp only [fieldDim,List.map_map]; rfl
lemma inv_dim (w : List (Lane4 G)): fieldDim wfield (invertMom w)=fieldDim wfield w:= by simp only [fieldDim,invertMom,List.map_map]; rfl
-- inheritance. `star` pull of ray jets analytic.
variable {h d:ℤ} {j:ℕ}
lemma read_star {f:ℝ→ℂ} (hf:ContDiff ℝ ∞ f): reading j (fun i=>star (f i))=star (reading j f):= by
   unfold reading; rw [star_smul,star_trivial]; congr 1
   unfold iteratedDeriv; let C:ℂ→L[ℝ] ℂ:= Complex.conjCLE.toContinuousLinearMap
   change iteratedFDeriv ℝ j (C ∘ f) _ _= C _; rw [C.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)]; rfl
lemma skin_shadow (hs: Solid b F d) (hw:Course b w) (hp: ContDiff ℝ ∞ fun x=> F (sail (ray w) x)): skin wfield h F (invertMom w)=star (skin wfield h F w):= by
    simp_rw [skin,inv_dim]; split
    · rw [torch_at,torch_at]; simp_rw [invert_sail, hs.real' _ (sail_course _ (ray_course hw)),read_star hp]
    simp
lemma skin_ghost (hs: Solid b F d) (hw:Course b w) (hp: fieldDim ghostNo w≠d): skin wfield h F w=0:= by
    unfold skin; split; swap; rfl
    rw [torch_at]; have he x : F (sail (ray w) x)=0:= hs.ghost _ (sail_course _ (ray_course hw)) (by rw [sail_dim,ray_dim]; exact hp); simp_rw [he]; simp [reading]
lemma skin_signed (hs: SignedScope b F) (w : List (Lane4 G)) (hw: Course b w) (u:Signed) : (w.map (negateField u)).prod * skin wfield h F (w.map (permute u))=skin wfield h F w:= by
    simp_rw [skin,sign_dim]; split
    · rw [torch_at,torch_at,← read_const]; simp_rw [ray_sail_sign]; congr; ext x; exact (by nth_rw 1 [← sign_const u w x]; exact hs u _ (sail_course _ (ray_course hw))) -- congr
    exact mul_zero _
lemma skin_swap (hs: Solid b F d) (l k) (i j : Lane4 G) (hw : Course b (l++i::j::k)): skin wfield h F (l++i::j::k)=cross (parity i.1) (parity j.1)*skin wfield h F (l++j::i::k) := by
   simp_rw [skin, show fieldDim wfield (l++j::i::k)=fieldDim wfield (l++i::j::k) by simp only [fieldDim,List.map_append,List.map_cons,List.sum_append,List.sum_cons]; abel]; split
   · rw [torch_at,torch_at,← read_const]; simp_rw [ray_go,List.map_append,List.map_cons]; apply congr_arg (reading _); ext x
     apply hs.symm (i:=(i.1,x • i.2)) (k:=(j.1,x • j.2)); have hv:= sail_course x (ray_course hw); simpa only [ray_go,List.map_append,List.map_cons] using hv
   exact Eq.symm (mul_zero _)

end YM.MS.High
