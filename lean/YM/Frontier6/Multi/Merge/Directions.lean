import YM.Frontier6.Multi.Merge.Vine

/-!
# along all arity footprints. Effects on the many-leaf decision.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road.Fork
open Function Filter Finset Set Spec Fareway Tale Lattice Next.Extract Cells MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}
variable {O: V→Type} [heO:∀ i,Fintype (O i)][htO:∀ i,DecidableEq (O i)]
variable (K:Final C F S) (u:Sigma O→ E4) (v:Sigma O→S.Tag)(c:V→E4)
set_option quotPrecheck false
variable (z: (Sigma O)×Axis) (k:ℕ) (a t:ℝ) (d:ℕ)
local notation "J"=> z.1.fst
local notation "o"=> z.1.snd
local notation "A"=> z.2
local notation "W"=> (z.1.snd, z.2)
lemma cutting_wag : cutTo z.1.fst (wag u a z t)=wag (cutTo z.1.fst u) a W t:=by
   ext1 i; by_cases h:i=o; subst i; change wag u a z t z.1=_; rw [wag_eq,wag_eq]; rfl
   change wag u a z t (Sigma.mk J i)=wag (cutTo J u) a W t i; rw [wag_untouched _ _ _ _ _ ?_, wag_untouched _ _ _ _ _ h]; rfl; exact fun he=> h (sigma_mk_injective (he.trans (Sigma.eta _).symm)) -- find
lemma cutting_route : cutTo J (route K v z k)=route K (cutTo J v) W k:=by
   ext1 i; by_cases h:i=o; subst i; simp only [cutTo, comp_apply]; change route K v z k z.1=_; unfold route; rw [update_self, update_self]; rfl
   unfold cutTo; dsimp only [comp_apply]; rw [route_same,route_same]; rfl; exact h; exact fun he=> h (sigma_mk_injective (he.trans (Sigma.eta _).symm))
lemma mediocre (i)(he:i≠J):cutTo i (wag u a z t)=cutTo i u:=funext fun j=> wag_untouched u _ z (Sigma.mk i j) t (fun hz=> he (congr_arg Sigma.fst hz))
lemma told (i)(he:i≠J):cutTo i (route K v z k)=cutTo i v:=funext fun j=> route_same K _ _ k (Sigma.mk i j) (fun hz=> he (congr_arg Sigma.fst hz))
lemma roots_rank : abroad K (wag u a z t) (route K v z k) d J= absorb K 0 d (assembly S (wag (cutTo J u) a W t) (route K (cutTo J v) W k)) :=by unfold abroad seedling; rw [cutting_wag,cutting_route]
lemma settle (i)(he:i≠J): packing K (wag u a z t) c (route K v z k) d i=packing K u c v d i:= by unfold packing abroad seedling; rw [mediocre _ _ _ _ _ he,told _ _ _ _ _ he]
lemma pickups : pickup (wag u a z t) c= wag (pickup u c) a z t:=by
   ext1 i; by_cases h:i=z.1; subst i; rw [wag_eq]; unfold pickup; rw [wag_eq]; unfold chord Ward.inc; abel
   rw [wag_untouched _ _ _ _ _ h]; unfold pickup; rw [wag_untouched _ _ _ _ _ h]

variable (s:StateIndex K) {r:ℝ} (he:Frontier6.Safe K d r)
def vibrating (t:ℝ):ℂ:= a^k • poll S (state K s) (combining K (wag u a z t) c (route K v z k) d)
lemma vibration (hp: snug 0 r (cutTo z.1.fst (wag u a z t))) (hQ:Injective (pickup (wag u a z t) c)) (he:Frontier6.Safe K d r) : HasDerivAt (vibrating K u v c z k a d s) (vibrating K u v c z (k+1) a d s t) t:=by
   rw [cutting_wag] at hp; rw [pickups] at hQ
   unfold vibrating combining; simp_rw [map_sub,smul_sub]; apply HasDerivAt.sub
   · simp_rw [pickups]; exact starter K (pickup u c) _ z k a s t hQ
   let p:=pickup u c; let X:=∏ i∈ Finset.univ.erase J,packing K u c v d i; let L:= (LinearMap.toContinuousLinearMap (readingMap K (c J) d X s)).restrictScalars ℝ
   let f(n):= drivers K (cutTo J v) (cutTo J u) W 0 d n a
   have hR(n)(t:ℝ): a^n • poll S (state K s) (∏ i:V,packing K (wag u a z t) c (route K v z n) d i)=L (f n t):=by
       rw [←mul_prod_erase _ _ (mem_univ J), prod_congr (s₂:=Finset.univ.erase J) (g:=packing K u c v d) rfl (fun j hj=> settle K u v c z n _ _ _ j (ne_of_mem_erase hj))]; change a^n • poll _ _ (letter S (c J) ⟨d,abroad K (wag u a z t) (route K v z n) d J⟩ * X)=_
       unfold f drivers; rw [map_smul, ← reads K, roots_rank]; rfl
   simp_rw [hR]; exact L.hasFDerivAt.comp_hasDerivAt t (driving K _ _ _ _ _ _ he a t hp)
end YM.Frontier6.Road.Fork
