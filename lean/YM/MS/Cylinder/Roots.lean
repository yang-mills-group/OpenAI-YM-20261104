import YM.MS.Cylinder.Bulk
/-!
# Apply the functional sum derivation before forming symbols

Working in translation algebra. Only ∆C bare local needs this; for P lines
 use the total-plane convention. ∆R identity later proves master. Wrap of this root
 to finite positions also described explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Lab
open Function Set Finset Koszul Plane
variable {R A B P Q J : Type*} [CommRing R] {p : Sector A} {s:Finset P} [AddCommGroup P]
local infixl:70 " ⋄ "=>couple (field p)
def spot (p:Sector A)(i j:A)(x:P)(F:Seed A P R): On A P R:= (couple (field p) (twisted (field p) (p j) (force i x F))).comp (enter (j,x)) +
   (couple (field p) (force j x (twisted (field p) (p i) F))).comp (enter (i,x))
lemma spot_eq (i j:A) (x:P) (F H:Seed A P R): spot p i j x F H= twisted (field p) (p j) (force i x F) ⋄ enter (j,x) H+force j x (twisted (field p) (p i) F) ⋄ enter (i,x) H:=rfl
private def want (p:Sector A)(i j:A)(F:Seed A P R): On A P R:= joinOne (fun x=>spot p i j x F) (fun H s h x hv=> by rw [spot_eq, notEnter H h (j,x) (fun hh=>hv hh),notEnter H h (i,x) (fun hh=>hv hh)]; simp)
private lemma want_at (F H:Seed A P R)(i j:A) (h:BoundBy (s:Set P) H): want p i j F H=∑ x∈s,spot p i j x F H:= join_k _ _ H h
def root (p:Sector A)(i j:A): Seed A P R→ₗ[R] On A P R where
   toFun:=want p i j
   map_add' F u:= by apply LinearMap.ext; intro H; obtain ⟨s,hs⟩:= obliges H; simp_rw [LinearMap.add_apply,want_at _ H i j hs, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; simp only [spot_eq,map_add,LinearMap.add_apply]; abel
   map_smul' c F:= by apply LinearMap.ext; intro H; obtain ⟨s,hs⟩:= obliges H; simp_rw [LinearMap.smul_apply,RingHom.id_apply,want_at _ H i j hs,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; simp only [spot_eq,map_smul,LinearMap.smul_apply,smul_add]
lemma root_at (F H:Seed A P R)(i j:A) (h:BoundBy (s:Set P) H): root p i j F H=∑ x∈s,spot p i j x F H:= want_at F H i j h
lemma root_all [Fintype P](F H:Seed A P R)(i j:A): root p i j F H=∑ x:P,spot p i j x F H:= by rw [root_at F H i j (show BoundBy (↑(Finset.univ (α:=P)): Set P) H from fun _ _ _ hx=> (hx (mem_univ _)).elim)]

-- Wrap and mole sites. Actually at arbitrary n, alias harmless for bracket; only need use sufficiently large.
variable [AddCommGroup Q] {r:P→+Q}
lemma trforce (i:A)(x:P)(F:Seed A P R)(h:BoundBy (s:Set P) F)(hr:InjOn r (s:Set P)): transport r (force i x F)=force i (r x) (transport r F):= by
    classical
    rw [force_at (s:=s.image r) (transport r F) (by rw [Finset.coe_image]; exact relax F h r), Finset.sum_image hr,force_at F h, map_sum]; apply Finset.sum_congr rfl; intro u hu; rw [trans_shift,map_sub,← transport_single r hr F h (i,u) hu]; rfl

lemma trroot (F H:Seed A P R)(i j:A)(h:BoundBy (s:Set P) F)(hv:BoundBy (s:Set P) H)(hr:InjOn r (s:Set P)): transport r (root p i j F H)=root p i j (transport r F) (transport r H):= by
    classical
    rw [root_at (transport r F) (transport r H) i j (s:=s.image r) (by rw [Finset.coe_image]; exact relax H hv r), Finset.sum_image hr,root_at F H i j hv,map_sum]; apply Finset.sum_congr rfl; intro x hx; simp_rw [spot_eq,map_add,transport_comes,← transport_single r hr H hv (j,x) hx,← transport_single r hr H hv (i,x) hx] -- `rw` match post
    rw [transport_sign, trforce i x F h hr, trforce j x (twisted _ _ F) (h.sign _) hr,transport_sign]; rfl

section finite
variable [Fintype P]
lemma force_sign (x:Bool) (F:Seed A P R): sumHome (twisted (field p) x F)= twisted (field p) x (sumHome F):=by
    rw [total_uses,total_uses,map_sum]; exact Finset.sum_congr rfl (fun i _=> transport_sign ..)
lemma pair_finite {i j:A} (F H:Seed A P R)(c:Bool)(h: (p j ^^ p i)=c)(x:P): (spot p i j x F H).val=link (diffPair (i,x) (j,x)) c (field p) (sumHome F).val H.val := by
    rw [link_pair (p:=field p) (i,x) (j,x) h]; simp only [spot_eq,add_stack,coupled,enterp,twistp,force_finite,force_sign]
lemma roots_finite {i j:A} (F H:Seed A P R)(c:Bool)(h:(p j ^^ p i)=c): (root p i j F H).val=link (∑ x:P,diffPair (i,x) (j,x)) c (field p) (sumHome F).val H.val:= by rw [root_all, sum_stack,link_sum]; simp_rw [pair_finite F H c h]
lemma root_shift {i j:A} (F H:Seed A P R)(x:P): root p i j F (Lab.Shift x H)= Lab.Shift x (root p i j F H):= by
    rw [root_all,root_all,map_sum]; have he z: Lab.Shift x (spot p i j z F H)=spot p i j (x+z) F (Lab.Shift x H):= by simp_rw [spot_eq,map_add,shift_couple,shift_enter H]; rw [show Shift x (twisted _ _ (force i z F)) = twisted (field p) (p j) (Shift x (force i z F)) from transport_sign ..,← forces,← forces, add_comm z x] -- ambiguous
    simp_rw [he]; exact (Equiv.sum_comp (Equiv.addLeft x) (fun z=> spot p i j z F (Lab.Shift x H))).symm
omit [AddCommGroup P] in
lemma heart_finite (i j:A)(F:Seed A P R): (heart i j F).val= (∑ x:P, diffPair (i,x) (j,x)) F.val:= by rw [heart_all,sum_stack]; simp only [diffPair_apply,enterp,LinearMap.sum_apply]
lemma home_heart (i j:A)(F:Seed A P R): (sumHome (heart i j F))= heart i j (sumHome F) := by rw [total_uses,total_uses,map_sum]; exact Finset.sum_congr rfl (fun i _=> heart_shift ..)
lemma home_root (i j:A)(F H: Seed A P R)(c:Bool)(h:(p j ^^ p i)=c): (sumHome (root p i j F H)).val = link (∑ x:P,diffPair (i,x) (j,x)) c (field p) (sumHome F).val (sumHome H).val:= by
   rw [← roots_finite _ _ _ h]; congr 1; rw [total_uses,total_uses,map_sum]; simp_rw [root_shift]
end finite
end YM.MS.Cylinder.Lab
