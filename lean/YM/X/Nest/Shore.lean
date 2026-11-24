import YM.X.Nest.Rays
/-!
# apertures on relative-marks frames and normalized term supports. Also useful for scalar unit mark.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Rays
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {V I T:Type*} {i k d:ℕ} {G:Gauge}
variable {q:ℕ+} (hq:1<q.val)(α:T→ℕ)(x:Fielding.Walk)(p:Word G)
section cost
variable (S:Finset I) (f:I→Fielding.Walk) (F:I→E4) (hf:∀ i∈S,plot q (f i) (F i)) (h: Set.InjOn F S)
include hq hf h
lemma rays_iso : Isolation (token α) (travelers α q G) S (fun i=>Meter q α (f i) G):= fun i hi j hj hn a ha b hb=> cost_paths hq _ (hf i hi) (hf j hj) (fun he=>hn (h hj hi he.symm)) a ha b hb
end cost
include hq
lemma carries_flat (P:ℕ→Curly G) (hp:P∈ Badge (Curly G) (Vanished q) (CakeH G))(n:ℕ): Carries q α x (fun t=> epsilon q (α t)^(-(n:ℤ)) • dress (x (α t)) (P (α t))):= by
    induction hp using Submodule.span_induction with
    | mem p h=>
       obtain ⟨c,v,hc,h,rfl⟩:=h; let c'(i):= epsilon q i ^ (-(n:ℤ)) • c i; let K(t:T):= dress (x (α t)) v; obtain ⟨k,H⟩:= transporting α x h hq; change (fun i:T=> _ • _)∈ Bag (token α) (Meter q α x G) k at H; simp only [Nat.cast_zero, neg_zero,zpow_zero,one_smul] at H
       rw [show (fun i:T=>_ • _)= charge (c' ∘ α)*K from ?_]; exact ⟨k,Bag.point (B:=token α) K H _ (rear α c' (late hq (eps_supp hc)))⟩
       rw [unify]; ext1 i; rw [map_smul]; exact (smul_assoc ..).symm
    | zero=> refine ⟨0,?_⟩; simp only [Pi.zero_apply,map_zero,smul_zero]; exact Submodule.zero_mem _
    | add a c _ _ y t=> simp only [Pi.add_apply,map_add,smul_add]; exact y.add α t -- theorem field notation hq first?
    | smul a b he h=> obtain ⟨n,x⟩:=h; refine ⟨n,?_⟩; simp_rw [Pi.smul_apply,map_smul,smul_comm (_:ℝ) a]; exact Submodule.smul_mem _ a x
lemma urban_cost : Carries q α x (urban q α p x):= by
    have ht:=carries_flat hq α x (fun i=> load q p i - Grow.looking p) (self_ration hq p) p.d -- looking
    have hg:=transporting α x (press_word p) hq
    suffices he:(fun i:T=>epsilon q (α i) ^(-(p.d:ℤ)) • dress (x (α i)) (load q p (α i)- Grow.looking p))+(fun i:T=> epsilon q (α i)^(-(p.d:ℤ)) • dress (x (α i)) (Grow.looking p))= urban q α p x by rw [← he]; exact ht.add α hg
    ext1; simp [urban,map_sub, smul_sub]
variable [DecidableEq I] (S:Finset I) (f:I→Fielding.Walk) (F:I→E4) (hf:∀ i∈S,plot q (f i) (F i)) (h: Set.InjOn F S) {r:ℝ}
local notation "U" => id (α:=ℕ)
local notation "P"=> travelers U q G
local notation "W"=> fun i:I=> Meter q U (f i) G
omit hq in
lemma token_id {a:ℕ→ℂ}(h:a∈token U): Released a:= by obtain ⟨b,h,rfl⟩:=h; exact h
omit hq in
lemma token_crew : Allows (token U) Shelf.crew:= fun x y hx hy=> breaths (token_id hx) hy
include hf h
variable {p':Code (Hair G) ℕ} {g:I→ Code (Hair G) ℕ}
lemma daylights (C':Submodule ℂ (T→ℂ))(g:I → Code (Hair G) T)(p':Code (Hair G) T) (hB:∀ i∈ S, Carries q α (f i) (g i))(hA:Allows (token α) C')(hp:Condition C' (travelers α q G) S (fun i=> Meter q α (f i) G) p') : lap S (travelers α q G) g p'∈C':= visits hA (rays_iso hq α S f F hf h) hp hB
lemma near_lap (hr:0≤r)(hp: ∀ i∈S,r < ‖F i‖)(hB:∀ i∈S,Carries q U (f i) (g i))(hZ:Apt q r p'): Released (lap S P g p'):= by
    refine daylights hq U S f F hf h _ _ _ hB token_crew ?_; intro l; induction l generalizing p' with
    | nil=> intro hl; change Released (fleet p'); exact hZ.use 0 Tide.empty
    | cons v l IH=>
       intro hl; obtain ⟨b,hb,y⟩:= hl v (by simp); obtain ⟨t,rfl⟩:=y
       let k:=t.k; let w:ℕ→Brush G:= fromP q k (f b) t.x
       have hx: Tide q r w:= from_tide hq hr (hp _ hb) (hf _ hb) t.x t.order t.sector
       have hy(i:ℕ): stream P (liftC q U (f b) t) p' i= stroke (w i) (p' i):= by rw [stream_point, liftC,palette];rfl
       rw [swarm]; refine IH ?_ (fun a hh=> hl a (List.mem_cons_of_mem _ hh)); -- specialize IH
       rw [show stream P _ p'= (fun i=> stroke (w i) (p' i)) from funext hy];exact hZ.stamp w hx
end YM.PositionX.Crate.Rays
