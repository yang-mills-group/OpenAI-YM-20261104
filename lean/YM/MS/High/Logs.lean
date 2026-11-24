import YM.MS.LandauMatch
import Mathlib.LinearAlgebra.Lagrange
/-!
# Logarithmic scale allowance

Use $y=\log μ$ as native argument of polynomial estimates. Full interpreter
in position comparison sets μ=a (in ren length units). `StringP` uses this one
variable helper independent of the spacetime polynomials and of gauge parameters.
Provides polynomial interpolation **with shared nodes** across test parameters.
Use it explicitly before needing to choose values at all y consistently.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Logarithm
open Function Filter Set Finset Real Polynomial Lagrange
open scoped Topology ContDiff
variable {ι α E F G : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

abbrev Poly := Polynomial ℝ
def interest (N : ℕ) (E : Type) [AddCommGroup E] [Module ℝ E] := Submodule.span ℝ {g : ℝ→E| ∃ (a : Poly), a.degree < (N:WithBot ℕ) ∧ ∃ v:E,g=(fun i=>a.eval i • v)}
def Ready (f : ℝ→E) : Prop:=∃ N, f∈ interest N E
lemma hire {N : ℕ} (p : Poly) (v : E) (h : p.degree<N) : (fun i=>p.eval i • v) ∈ interest N E:= Submodule.subset_span (mem_setOf.mpr ⟨p,h,v,rfl⟩)
lemma widens {a b :ℕ} (h:a≤b) : interest a E ≤ interest b E := by refine Submodule.span_mono ?_; rintro x ⟨p,hp,v,rfl⟩; exact ⟨p,lt_of_lt_of_le hp (Nat.cast_le.mpr h),v,rfl⟩
lemma status (p : Poly) (v : E): Ready (fun i=> p.eval i • v):= ⟨p.natDegree+1,hire p v (lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast (show (p.natDegree:ℕ)<p.natDegree+1 from p.natDegree.lt_add_one)))⟩ -- simplify
namespace Ready
variable {f g : ℝ → E}
lemma scale (h : Ready f) (c:ℝ) : Ready (c • f) := by obtain ⟨N,h⟩:=h; exact ⟨N,Submodule.smul_mem _ _ h⟩
lemma add (h : Ready f) (e : Ready g) : Ready (f+g) := by obtain ⟨N,h⟩:=h; obtain ⟨M,e⟩:=e; exact ⟨max N M,Submodule.add_mem _ (widens (le_max_left ..) h) (widens (le_max_right ..) e)⟩
lemma zero : Ready (0:ℝ→E):= ⟨0,zero_mem _⟩
lemma neg (h : Ready f) : Ready (-f) := by simpa using h.scale (-1)
lemma sub (h : Ready f) (H : Ready g): Ready (f-g):=by simpa [sub_eq_add_neg] using h.add H.neg
lemma sums (s : Finset α) {k : α → ℝ→ E} (h : ∀ i∈s,Ready (k i)): Ready (∑ i∈s, k i) := by
   classical
   induction s using Finset.induction with
   | empty => simpa using zero (E:=E)
   | insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma const (f:E): Ready (fun _ => f):= by simpa using status (1:Poly) f
lemma add_point (h : Ready f) (e : Ready g) : Ready (fun i=> f i+g i):= add h e
lemma scale_p (h : Ready f) (v:ℝ): Ready (fun i=>v • f i):=scale h v
lemma Ind {p : (ℝ→E) → Prop} (h : Ready f) (hh : ∀ (a:Poly) v,p (fun i=>a.eval i • v)) (hz:p 0) (hA : ∀ f g,p f → p g → p (f+g)) (hB : ∀ (c:ℝ) f,p f→p (c • f)): p f:= by
    obtain ⟨N,h⟩:=h; refine Submodule.span_induction (p:=fun f _=>p f) ?_ hz (fun i j _ _=> hA i j) (fun i j _=> hB i j) h
    rintro v ⟨f,hf,v,rfl⟩; exact hh ..
lemma linear (h : Ready f) (L : E→ₗ[ℝ] F): Ready (fun x=>L (f x)) := h.Ind (p:=fun f=> Ready (fun x=>L (f x))) (fun a v=> by simpa only [map_smul] using status a (L v)) (by simp; exact zero) (fun x y hx hy=> by simpa only [Pi.add_apply,map_add] using add_point hx hy) (fun c x h=> by simpa only [Pi.smul_apply,map_smul] using scale_p h c)
lemma pmul (p : Poly) (H : Ready f) : Ready (fun i=>p.eval i • f i):= by
   refine Ready.Ind (p:=fun f=> Ready (fun i=>p.eval i • f i)) H ?_ ?_ ?_ ?_
   · intro a v; simpa only [smul_smul,eval_mul] using status (p*a) v
   · simp; exact zero
   · intro x y hx hy; simpa only [Pi.add_apply,smul_add] using add_point hx hy
   intro c x hx; simpa only [Pi.smul_apply,smul_comm (p.eval _) c] using scale_p hx c
lemma pair {g : ℝ→F} (L : E→ₗ[ℝ] F→ₗ[ℝ] G) (h : Ready f) (hg : Ready g): Ready (fun i=> L (f i) (g i)) := by
   refine Ready.Ind (p:=fun f=> Ready (fun i=>L (f i) (g i))) h ?_ ?_ ?_ ?_
   · intro a v; simpa only [map_smul, LinearMap.smul_apply] using pmul a (hg.linear (L v))
   · simp; exact zero
   · intro x y hx hy; simpa only [Pi.add_apply,map_add,LinearMap.add_apply] using add_point hx hy
   intro c x hx; simpa only [Pi.smul_apply,map_smul,LinearMap.smul_apply] using scale_p hx c
lemma smul {p: ℝ→ℝ} (h: Ready p) (hf : Ready f): Ready (fun x=>p x • f x):= h.pair (LinearMap.lsmul ℝ E) hf
lemma scalar {p : ℝ→ℝ} (h : Ready p): ∃ a:Poly,p=(fun i=>a.eval i):= by
   refine Ready.Ind (p:=fun p=> ∃ a:Poly,p=(fun i=>a.eval i)) h ?_ ?_ ?_ ?_
   · intro a x; exact ⟨a*Polynomial.C x,funext fun _=> by simp⟩
   · exact ⟨0,funext fun _=>by simp⟩
   · rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,funext fun _=> by simp⟩
   rintro c x ⟨a,rfl⟩; exact ⟨Polynomial.C c*a,funext fun _=>by simp⟩
lemma got (a : Poly): Ready (fun i=> a.eval i):= by simpa using status a (1:ℝ)
end Ready

-- interpolation expression lives in real-log space
def plate (N j : ℕ) : Poly := Lagrange.basis (Finset.range N) ((↑) : ℕ→ℝ) j
def evaluate (N : ℕ) (f : ℝ→ E) (s:ℝ): E:= ∑ i∈Finset.range N,(plate N i).eval s • f i
lemma eval_ready (N : ℕ) (f : ℝ→E): Ready (evaluate N f):= by
   convert Ready.sums (Finset.range N) (fun i _ => status (plate N i) (f i)) using 1; ext; rw [Finset.sum_apply]; rfl
lemma interpret {N:ℕ} {f : ℝ→E} (hf:f∈interest N E) (i:ℝ): f i=evaluate N f i:= by
    let L : (ℝ→E)→ₗ[ℝ] E := ∑ j∈Finset.range N, (plate N j).eval i • LinearMap.proj (j:ℝ)
    have hL f:evaluate N f i=L f:= by unfold evaluate L; simp only [LinearMap.sum_apply]; rfl
    have hp (a:Poly) (H:a.degree<N): a.eval i=∑ j∈ Finset.range N,(plate N j).eval i * a.eval (j:ℝ):= by
        have Hv:= Lagrange.eq_interpolate (s:=Finset.range N) (v:= ((↑):ℕ→ℝ)) Nat.cast_injective.injOn (by simpa using H)
        have hc:= congr_arg (Polynomial.eval i) Hv; simpa [Lagrange.interpolate,plate,eval_finsetSum,mul_comm] using hc
    rw [hL]; refine Submodule.span_induction (p:=fun f _=>f i=L f) ?_ (by simp) (fun f g h hh he hu=>by simp [he,hu]) (fun a v hh he=>by simp [he]) hf
    rintro f ⟨a,ha,v,rfl⟩; rw [← hL]; dsimp only [evaluate]; nth_rw 1 [hp a ha]; simp only [sum_smul, smul_smul]
end YM.MS.Logarithm
