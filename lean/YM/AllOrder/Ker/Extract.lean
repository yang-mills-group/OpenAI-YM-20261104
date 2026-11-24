import YM.AllOrder.Ker.Seats
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker
open Lattice Laurent Bloch Matrix Complex RG Push.Uniform Precision Push
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Primitives.TwoWave Primitives.TwoWave.RealSlice Further.PhysicalPeriodLimitF933 Shingle Macrame
open scoped BigOperators Topology Classical ContDiff
variable {n m : Side} {α β : Type} [Fintype α] [Fintype β] {k M : ℕ}
variable {C a:ℝ} {G : Mat n α β k}
namespace Sampling
def at_zero (G : Mat n α β k): Fan α β k:= fun i t w=> G (0,i) (floated 0 t w)
def immature (G : Mat n α β k) : Fan α β k:=fun i t w=> if w= pristine (0:Site n) (floated (0:Site n) t w) then at_zero G i t w else 0
open Filter
omit [Fintype α]
omit [Fintype β] in
lemma wore {w:Shift (Arm k)} (t:Fin k→β)(x y:Site n) : pristine x (floated x t w)=pristine y (floated y t w):=by funext j; rcases j with ⟨j,k⟩; simp [pristine,floated]
omit [Fintype β] in
lemma slant (h:Stilled G)(u x:Site n)(i:α)(t:Fin k→β)(w:Shift (Arm k)) : G (u,i) (floated u t w)=G (x,i) (floated x t w) := by
 have he:=h (x-u) (u,i) (floated u t w); apply he.symm.trans ?_; congr 1; · change (u+(x-u),i)=(x,i); rw [add_sub_cancel u x] -- formula?
 ext1 j; apply Prod.ext; · change (u+wrap _ _)+(x-u)=x+_; abel
 rfl
lemma folded (W:Window n m M){V:Mat m α β k}(h:Same G V W) (hv:Stilled V) (x:Leaf m α) (t:Fin k→Leaf n β):
   pieces (immature V) n (BookM W α x) t= G (BookM W α x) t := by
  -- sum over all w equal finite
  classical
  unfold pieces; rw [h x t]
  let z:=x.1; let A:=W.cut z; let S:=robe W t; let F:=fun y:Fin k→ Leaf m β=>pristine z y
  have hY(v:Fin k→Leaf m β)(he:v∈S): Prod.snd ∘ v= Prod.snd ∘ t:= by funext j; exact congr_arg Prod.snd (congr_fun ((tried ..).1 he) j)
  have hi(v:Fin k→Leaf m β)(he:v∈S): floated z (Prod.snd ∘ t) (F v)=v:= by rw [← hY _ he]; exact frock ..
  have hh : Set.InjOn F ↑S:= fun i hI j hj h=> by rw [← hi i hI, h,hi j hj]
  -- need Fintype β omitted? remove omit persistent?
  rw [tsum_eq_sum (s:=S.image F),Finset.sum_image hh]
  · refine Finset.sum_congr rfl fun i he=> ?_
    have hx : t= floated A (Prod.snd ∘ t) (F i) := by rw [← (wheel W z (Prod.snd ∘ t) A (F i)).2 (fun _=>rfl),hi _ he]; exact ((tried ..).1 he).symm
    rw [if_pos (show t = floated (BookM W α x).1 (Prod.snd ∘ t) (F i) from hx)]; unfold immature at_zero
    rw [← wore (Prod.snd ∘ t) z (0:Site m),hi _ he, if_pos rfl,slant hv _ z, hi _ he]; rfl
  intro w he; split; swap; rfl
  rename_i hy; unfold immature; split; swap; rfl
  rename_i hz
  let V':=floated z (Prod.snd ∘ t) w; have hp : V'∈S:= by
    apply (tried ..).mpr; rw (occs:=.pos [1]) [show V'=floated z (Prod.snd ∘ t) w from rfl,(wheel W z (Prod.snd ∘ t) A w).2 (fun _=>rfl)]; exact hy.symm
  exact (he (Finset.mem_image.mpr ⟨V', hp,((wore ..).trans hz.symm)⟩)).elim
-- F constructor compiling
omit [Fintype β] in
lemma bolts (h:Room G a C)(hx:0 ≤ C)(ha:0≤a) (i t w): |immature G i t w| ≤ C*Real.exp (-a/4*size w) := by
   unfold immature; split; rename_i he;
   · refine (h _ _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hx)
     let v := floated (0:Site n) t w; let b : ℕ:=∑ i:Fin k,separation (0:Site n) (v i).1; have hp : size w ≤ 4*b:= (congr_arg size he).trans_le (tour ..)
     have hq : (size w:ℝ) ≤ 4*(b:ℝ) := by exact_mod_cast hp
     change -a*(b:ℝ) ≤ -a/4*_ ; nlinarith [hq]
   rw [abs_zero]; positivity
-- fix F.
end Sampling
open Sampling
section Result
open Filter
-- common strip cap of any projector lift, preserves polynomial costs
abbrev small_a (a:ℝ):= a/8
def boltC (k:ℕ) (a:ℝ):= (2*((1+small_a a)/small_a a))^(Fintype.card (Arm k))
omit [Fintype β] in
lemma boltC_pos (k:ℕ)(h:0<a): 0<boltC k a:= by unfold boltC small_a; positivity -- issue omit [ ] unused variables α β not scope
omit [Fintype α] [Fintype β] in
lemma headway {F:Fan α β k} (h:∀ i t w,|F i t w|≤ C*Real.exp (-a/4*size w))(ha:0<a)(hC:0≤C): Cap F (small_a a) (C*boltC k a) := by
 intro i t; let k' := small_a a; have hk:0<k':= by unfold k' small_a; positivity
 let f w:= F i t w; have hx (w : Shift (Arm k)) : Real.exp (k'*size w)*‖f w‖ ≤ C*Real.exp (-k'*size w):= by
    rw [Real.norm_eq_abs]; refine (mul_le_mul_of_nonneg_left (h i t w) (Real.exp_pos _).le).trans_eq ?_; rw [mul_left_comm,← Real.exp_add]; unfold k' small_a; congr 2; ring
 have he:= Width.compactPay (α:=Arm k) k' hk; let S:= (he.2.1.mul_left C).of_nonneg_of_le (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hx; refine ⟨fun i=>by positivity,S, (S.tsum_le_tsum hx (he.2.1.mul_left C)).trans ?_⟩
 rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he.2.2 hC
variable {Ad:Side→Prop}
structure Keep (G:Mats α β k) (Ad:Side→Prop): Prop where
 same : ∀ n,Ad n→Stilled (G n)
 multiple : ∀ n m:Side, Ad m → Ad n → ∀ t:ℕ, ∀ ht:m.val=n.val*t, Same (G n) (G m) (Macrame.normal ⟨t,ht⟩ ht)
-- omit [Fintype α] persistent undo; name inst?
end Result
-- restore
variable (α' : Type) -- name
omit [Fintype β] in
lemma chosen_le (d m:ℕ) : d+m+1 ≤ Nat.factorial (d+m+1) := by rw [Nat.factorial_succ]; exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)

-- restore actual [Fintype] by section? override
section final
open Filter
variable {α' β' : Type} [Finite α'] [Fintype β'] {Ad:Side→ Prop}
-- rename
lemma obtain_fan {G : Mats α' β' k} (h0:Often Ad) (H: Keep G Ad) (ht:∀ n,Ad n→ Room (G n) a C)(ha:0<a)(hC:0 ≤ C) : ∃ F:Fan α' β' k, Cap F (small_a a) (C*boltC k a) ∧ ∀ n, Ad n → G n=pieces F n:= by
 classical
 rcases h0 with ⟨d,hd⟩; let v(i:ℕ):Side:= ⟨Nat.factorial (d+i+1),Nat.factorial_pos _⟩; have hv(i:ℕ):=chosen_le d i; change ∀ i:ℕ,d+i+1≤(v i).val at hv; have hh(i:ℕ): Ad (v i):= hd _ ((show d≤d+i+1 by omega).trans (hv i))
 let f (i:ℕ):Fan α' β' k:= immature (G (v i)); let U:=α'×(Fin k→β')×Shift (Arm k); let F (i:ℕ) (x:U):=f i x.1 x.2.1 x.2.2
 let g (w:Shift (Arm k)) := C*Real.exp (-a/4*size w); have hw i (x:U):F i x∈ Metric.closedBall 0 (g x.2.2):= by simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] using! bolts (ht _ (hh i)) hC ha.le x.1 x.2.1 x.2.2
 obtain ⟨A,hA,s,hs,Hs⟩:= (isCompact_pi_infinite (fun x:U => isCompact_closedBall (0:ℝ) (g x.2.2))).tendsto_subseq (x:=F) (fun i _=> hw i _)
 let Z : Fan α' β' k := fun i t w=> A (i,t,w)
 have hz(i t w): Tendsto (fun j=> f (s j) i t w) atTop (𝓝 (Z i t w)):= tendsto_pi_nhds.mp Hs (i,t,w)
 refine ⟨Z,headway (fun i t w=> le_of_tendsto (hz i t w).abs (Eventually.of_forall (fun j=> bolts (ht _ (hh (s j))) hC ha.le i t w))) ha hC,?_⟩
 intro n hn; have hu : ∀ᶠ i in atTop,n.val∣(v i).val:=by filter_upwards [eventually_ge_atTop n.val] with i hi; exact Nat.dvd_factorial n.property (by omega)
 funext i t; -- ext expands? prefer funext
 let B := fun j w=> if t=floated i.1 (Prod.snd ∘ t) w then f (s j) i.2 (Prod.snd ∘ t) w else 0
 have hb : (fun j => ∑' w,B j w) =ᶠ[atTop] fun _=>G n i t:= by
    filter_upwards [hs.tendsto_atTop.eventually hu] with j hj; rcases hj with ⟨b,h⟩
    let W:=Macrame.normal (show n.val∣(v (s j)).val from ⟨b,h⟩) h; obtain ⟨x,hx⟩:= Macrame.seeds (n:=n) (N:=v (s j)) ⟨b,h⟩ i.1; change W.cut x=i.1 at hx; let p : Leaf (v (s j)) α':=(x,i.2); have hI : BookM W α' p=i:= Prod.ext hx rfl; have hj := Sampling.folded W (H.multiple n (v (s j)) (hh _) hn b h) (H.same _ (hh _)) p t; rw [hI] at hj; exact hj
 let R w:= if t=floated i.1 (Prod.snd ∘ t) w then Z i.2 (Prod.snd ∘ t) w else 0
 have he(w:Shift (Arm k)) : Tendsto (fun j=>B j w) atTop (𝓝 (R w)):= by
   unfold B R; split <;> rename_i hw; · simpa only [if_pos hw] using hz i.2 (Prod.snd ∘ t) w -- hw t eq causes recursion?
   simpa only [if_neg hw] using (tendsto_const_nhds : Tendsto (fun (_:ℕ)=> (0:ℝ)) atTop (𝓝 0))
 have hw j w : ‖B j w‖ ≤ g w := by unfold B; split; exact bolts (ht _ (hh (s j))) hC ha.le _ _ _; rw [norm_zero]; unfold g; positivity -- g unfold
 have h : 0<a/4:=by positivity
 have hS : Summable g:= by unfold g; rw [neg_div]; exact (Width.compactPay _ h).2.1.mul_left C
 exact tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds (tendsto_tsum_of_dominated_convergence hS he (Eventually.of_forall hw)) hb.symm
end final
end YM.AllOrder.Ker
