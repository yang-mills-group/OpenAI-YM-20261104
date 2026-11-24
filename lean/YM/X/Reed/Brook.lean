import YM.X.Reed.Rifle
import YM.X.Reed.Swish
/-! # K-Taylor peeling. Choose data ending in polynomial at order n-1. Using integration by parts stencils for highest moment. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Next.Rank.Beamer Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell Asymptotics
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {V:Type*} [NormedAddCommGroup V][NormedSpace ℝ V] {n k m:ℕ}
variable {R:ℕ→ℕ}{C:ℕ→ℝ}{A:ℕ→Brush G}
local notation "Fℕ"=>(atTop:Filter ℕ)
def ClearK (A:ℕ→Brush G):Prop:= ∀ j z, ∀ᶠ k:ℕ in Fℕ, orderK j (A k) z=0
lemma tree (X:ℕ→Okay G n): ClearK (fun k=> launch (X k)):= fun j z=>Eventually.of_forall fun k=> congr_fun (K_bound ..) _ -- inspect
lemma ClearK.gr (h:ClearK A) {B:ℕ→ Brush G}(p:ClearK B): ClearK (A-B):= by
    intro j z; filter_upwards [h j z,p j z] with k hk hp; rw [Pi.sub_apply,map_sub, Pi.sub_apply,hk,hp,sub_self]
omit [NormedSpace ℝ V] in
lemma eventually_zero {f:ℕ→Cover→V}(h:∀ z, ∀ᶠ k in Fℕ,f k z=0)(v:Fin n→Axis)(z:Cover): ∀ᶠ k in Fℕ, jumps n v (f k) z=0:= by
    induction n generalizing f with
    | zero=> exact h z
    | succ n IH=>
       simp_rw [jumps]; exact IH (fun x=> ((h (x+step (v 0))).and (h x)).mono (fun k ⟨hk,hp⟩=> by unfold stepValue; rw [hk,hp,sub_self])) _
lemma isBigO_zero_late {f:ℕ→V}(h:∀ᶠ k in Fℕ, f k=0): f=O[Fℕ] C:=by
    apply isBigO_iff.mpr; exact ⟨0, h.mono (fun i hi=> by rw [hi,norm_zero,zero_mul])⟩

def Bark (R:ℕ→ℕ)(C:ℕ→ℝ)(n m:ℕ)(A:ℕ→Brush G): Prop := ∀ j (l:Fin n→Axis), OnStreet R C m (fun k=> jumped l (raising j (A k)))
lemma larger(p:Specs G n)(j:Axis){k:ℕ}(h:n<k)(l:Fin k→Axis): jumped l (raising j (port n p))=0:= by rw [eg]; exact higher (p.sym j) _ h l
lemma roam (h:Bark R C k m A)(p:ℕ→Specs G n)(he:n<k): Bark R C k m (fun i=> A i-port n (p i)):= by
    intro j l; refine (h j l).move (Eventually.of_forall ?_); intro t; dsimp only; rw [map_sub,map_sub,larger _ _ he,sub_zero]
lemma stride (h: Bark R C (n+1) m A)(p:∀ j(l:Fin n→Axis),(fun k=>jumped l (raising j (A k)) 0)=O[Fℕ] C): Bark R C n (m+1) A:= by
    intro j l; refine OnStreet.of_step (p j l) ?_; intro i; refine (h j (Fin.cons i l)).move (Eventually.of_forall ?_); intro t; exact (steps n i l _).trans (hopped n i l _)

lemma shock (hr:Tendsto R atTop atTop)(h:Bark R C (n+1) m A)(p:ClearK A):
    (fun k=>seethe n (seeP n (A k)))=O[Fℕ] C:= by
    cases n with
    | zero=>
       apply isBigO_zero_late (Eventually.of_forall fun i=>(show seeP 0 (A i)∈ LinearMap.ker (seethe 0) from by rw [seethe_ker]; exact funext (heat_root (seeP 0 (A i)))))
    | succ n=> cases n with
      | zero=>
         apply isBigO_zero_late (Eventually.of_forall fun i=>(show seeP 1 (A i)∈ LinearMap.ker (seethe 1) from by rw [seethe_ker]; exact funext (heat_low (seeP 1 (A i)))))
      | succ n=>
         apply isBigO_pi.mpr; intro j; apply isBigO_pi.mpr; intro v
         let l : Fin n→Axis:= fun i=>v (i.cast (by omega))
         have he : v=(fun i: Fin (n+2-2)=> l (i.cast (by omega))):= by funext i; unfold l; congr 1
         let Q k:= seeP (n+2) (A k); let B(k:ℕ):= A k-port (n+2) (Q k)
         change (fun k=>seethe (n+2) (Q k) j v)=O[Fℕ] _; rw [he]; simp_rw [sizzle n]
         have hb : Bark R C (n+2) (m+1) B:= stride (roam h Q (by omega)) (fun j l=> isBigO_zero_late (Eventually.of_forall (fun k=> gone l (A k) j)))
         have hv (j:Axis)(l:Fin (n+2)→Axis)(z:Cover):(fun k=> jumps (n+2) l (raising j (B k)) z)=O[Fℕ] C:= (hb j l).ground (hr.eventually (eventually_ge_atTop (street z)))
         let D (X:ℕ→Brush G):= fun k:ℕ=> jumped l (orderK j (X k)) (0:Cover); have h₁: D B=O[Fℕ] C:= by
            unfold D; simp_rw [next_K]; apply IsBigO.neg_left; apply IsBigO.sum -- name
            intro i _; exact (hv ..).sub (hv ..)
         have hp : D A=O[Fℕ] C:= isBigO_zero_late (eventually_zero (p j) l 0)
         refine (hp.sub h₁).congr_left ?_; intro k; unfold D B; simp only [map_sub,Pi.sub_apply]; rw [jumpIt l (orderK _ (port _ _))]; abel -- adjust

lemma budget_lm {E' : Type*} [NormedAddCommGroup E'][NormedSpace ℝ E'][FiniteDimensional ℝ E']{f:ℕ→E'}(L:E'→ₗ[ℝ] V)(h:f=O[Fℕ] C): (L ∘ f)=O[Fℕ] C:= (L.toContinuousLinearMap.isBigO_comp _ _).trans h

def reachL (n:ℕ)(A:Brush G):= strikeP n (seeP n A)
lemma shrank (hr:Tendsto R atTop atTop)(h:Bark R C (n+1) m A)(p:ClearK A):
      Bark R C n (m+1) (fun k=> A k-launch (reachL n (A k))):= by
    let Q k:= seeP n (A k); let B k:= reachL n (A k); let c k:= (B k).val; refine stride (roam h c (by omega)) (fun j l=> ?_)
    have H:(seethe n ∘ Q)=O[Fℕ] C:= shock hr h p
    let K: Specs G n→ₗ[ℝ] G.Color:= (LinearMap.proj (0:Cover)) ∘ₗ jumped l ∘ₗ raising j ∘ₗ port n
    refine (budget_lm K (shoots H)).congr_left (fun k=>?_); have he : jumped l (raising j (A k)) 0= K (Q k):=(earns l (A k) j 0).symm
    simp only [comp_apply,map_sub,Pi.sub_apply,he]; rfl
end YM.PositionX.Reed
