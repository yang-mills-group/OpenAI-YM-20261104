import YM.MSbar.Ward.Polar
/-! In zero-loop (in actual integrated loops) sector there's no regular term at positive ℏ
order except the analytic continuations of OTHER ℓ sectors. No evanescent trace over K edges. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play.Produce
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Deck Work Ken
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{c d e:Bit}{k n i:ℕ}{P : Sites C}{R:ℝ}{z:ℂ}(X:Pulse W)

private lemma load : Apert (Scale.mass X.law 0 0) (cap X.law):= clears (n:=0) Profit.around (Nat.zero_le 0)
private def sol : Homo (Deck W 0) (Deck W 0):={toFun:=fun x=>⟨solve _ (cap X.law) x.val,admitted x.property (load X)⟩,map_add':= fun x y=> Subtype.ext (by
    funext n t; change Flight.rollout _ _ (ray (x.val+y.val) t) 1=_; rw [ray_add,Flight.plus (great_ray x.property _) (great_ray y.property _) (load X _)]; rfl),map_smul':=fun c x=>Subtype.ext (by
    funext n t; change Flight.rollout _ _ (ray (c • x.val) t) 1=_; rw [ray_scale,Flight.scalar (great_ray x.property _) (load X _)]; rfl)}
lemma seek_val (F:ListV C)(E:F 0=0)(h:Window W c R P)(H:∀ a i:ℕ, a+i < k+n→ Peak W 0 i (F a i 0)): Peak W c n (seek (Work.tree h (show c=c+0+0 by simp)) F F k n 0):= by
   simp_rw [seek, Finset.sum_apply]; apply Peak.sum; intro i hi; apply Peak.sum; intro j hj; obtain hx:i.1+i.2=k :=Finset.mem_antidiagonal.mp hi; obtain hy:j.1+j.2=n:= Finset.mem_antidiagonal.mp hj
   by_cases he:i.1=0; rw [he,E,Pi.zero_apply,make_nil]; exact Peak.zero _
   by_cases hh:i.2=0; rw [hh,E,Pi.zero_apply,make_rnil]; exact Peak.zero _
   rw [← hy]; unfold make; simp only [Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; exact Peak.polarized (fun _=> tree_plain h _) (H i.1 j.1 (by omega)) (H i.2 j.2 (by omega)) -- danger rewrite hy h
lemma first_sector (F:ListV C)(E:F 0=0)(H:∀ a i:ℕ, a+i<k+n→Peak W 0 i (F a i 0)): Peak W 0 n (Score X F k n 0):= Peak.lift (show Peak W 0 n (tripped (L X) (F k) n 0) from (by cases n <;> exact Peak.zero _)) (Peak.scale (seek_val F E X.pay H) _)
lemma tab (g:Film C)(h:Peak W 0 n (g 0)): Peak W 0 n (tabs X g k n 0):= by
   rw [show tabs X g k n 0=Play.post (fun _=>sol X) (g 0)+head X k n 0 from ?_]; swap
   · funext z; simp only [tabs,Nat.zero_le,↓reduceIte,Pi.add_apply,no_add]; unfold Play.post; change _ = solve _ _ (plug W 0 _).val + _; rw [no_add,plug_eq (h.besides z)]
   refine Peak.lift (Peak.cold_post _ h) ?_; cases n
   · exact Peak.ctr (by simpa only [head,and_self,↓reduceIte] using (show Sun W 0 (liftV (X.seed k)) from ⟨_,X.calm k,rfl⟩))
   simp only [head, Nat.succ_ne_zero,false_and,↓reduceIte]; exact Peak.zero _
-- at n=0 there's only the regular tree, so no pole subtraction, including contact kernels
lemma street (g:Film C)(h:Peak W 0 0 (g 0)): Counter.principal W 0 (hood 0) (scan 0 (scope 0) (tabs X g k 0))=0:=by
    simp only [scope,Nat.zero_add,scan_zero,Finset.range_one, Finset.sum_singleton]; obtain ⟨Y,hY,J⟩:= Peak.constant (tab (k:=k) X g h); rw [J]; exact is_principal (G:=0) (by simpa using Bright.regular (cold (U:=hood 0) hY)) (Winter.empty_free 0)
lemma lands (k n:ℕ): Peak W 0 n (evolve X k n 0):= by
    suffices hh:∀ v a b:ℕ,a+b=v→ Peak W 0 b (evolve X a b 0) from hh _ _ _ rfl
    intro v; induction v using Nat.strong_induction_on with
    | h v ih=> intro k n h; cases k with
          | zero => rw [initial]; exact Peak.zero _
          | succ i=> have H:=first_sector (k:=i+1) (n:=n) X _ (initial X) (fun a b hp=> ih _ (by omega) _ _ rfl); rw [grow X (by omega)]; unfold prepare clean; rw [if_pos rfl]; cases n with
                     | zero => rw [street X _ H,sub_zero]; exact tab _ _ H
                     | succ n => apply Peak.sub (tab X _ H); apply (Peak.negc (by omega)).mpr; obtain ⟨_,h⟩:=stairs X (F:=evolve X) (k:=i+1) (n:=n+1) (solve_part X); exact ⟨_,(Coherent.harmony (fun i hi=>h i)).pair.1⟩
lemma route_seed {z:ℂ}: Flat (evolve X k 0 0 z-X.seed k):=by
   cases k with
   | zero=> rw [initial,X.start]; change Flat ((0:Vertex C)-0); rw [sub_self]; exact Flat.none
   | succ i=> have H:=first_sector (k:=i+1) (n:=0) X _ (initial X) fun v j _=> lands X v j
              rw [grow X (by omega),prepare,clean, if_pos rfl,street X _ H,Pi.sub_apply,Pi.zero_apply,sub_zero,tabs,head]; simp only [le_refl, ↓reduceIte, and_self,liftV, add_sub_cancel_right, no_add]; exact Flat.solves ((scored (k:=i+1) (n:=0) X (F:=evolve X) 0 z)) (stair X _) (by simpa only [no_add] using load X)

namespace Shield
variable {X}(A:Shield X)
lemma snow (k n:ℕ): Peak W 1 n (flux A (evolve X) k n 0):= by
   refine Peak.sub (Peak.lift (?_:Peak _ _ _ ((Play.post A.R0) (evolve X k n 0))) (Peak.scale (seek_val _ (initial X) A.hd (fun a i _=> lands X ..)) _)) (?_:Peak W 1 n (tripped A.D0 _ n 0)); swap; cases n <;> exact Peak.zero _
   rw [show A.R0= fun _=> A.R0 0 from funext fun z=> Ken.arrow_plain A.hw _]; exact Peak.cold_post _ (lands X k n)
end Shield
end YM.MSbar.Play.Produce
