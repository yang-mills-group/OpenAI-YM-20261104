import YM.XSpace.Molo

/-!
# Ward counterterm decomposition with quantitative cost and convergence
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Uptown
open Function Filter Set Scale Mu Lattice Finsupp MvPolynomial Next.Rank.Normal Contraction Trace Chart2 Prelude Lows Drama Future
open scoped Topology BigOperators ContDiff

private lemma vouchers {K V I T:Type*}[NontriviallyNormedField K][AddCommGroup V][Module K V][FiniteDimensional K V]{L: Filter I} {f:T→ Module.Dual K V} {g: Module.Dual K V}{p:I→V}(h:∀ x,(∀ t,f t x=0)→g x=0)(ht:∀ x,Likely L fun i=> f x (p i)): Likely L fun i=> g (p i):=by
  classical
  let A (s:Finset T):=⨅ i:s, LinearMap.ker (f i.val); let B (s:Finset T):= Module.finrank K (A s); let Q(n:ℕ):= ∃ i,B i=n; have he:∃ n,Q n:= ⟨_,∅,rfl⟩
  obtain ⟨s,hs⟩:= (show Q (Nat.find he) from Nat.find_spec he)
  have hu (i:T) : A (insert i s)=A s := Submodule.eq_of_le_of_finrank_le (by intro p h; exact (Submodule.mem_iInf _).mpr fun j:s=> (Submodule.mem_iInf _).mp h (⟨j,Finset.mem_insert_of_mem j.property⟩:↥(insert i s))) (show B s ≤B (insert i s) by rw [hs]; exact Nat.find_min' he ⟨_,rfl⟩)
  have h':A s ≤ LinearMap.ker g:=by intro x hx; exact h x fun i=> (Submodule.mem_iInf _).mp (show x∈ A (insert i s) from (hu i).symm ▸ hx) ⟨_,Finset.mem_insert_self ..⟩
  have hw:= mem_span_of_iInf_ker_le_ker (L:=fun i:s=> f i.val) h'; clear h' h
  induction hw using Submodule.span_induction with
  | mem x h=> obtain ⟨t,rfl⟩:=h; exact ht t.val
  | zero=> simp_rw [LinearMap.zero_apply]; apply Likely.zero
  | add a b _ _ ih ih' => exact ih.add ih'
  | smul a b _ ih => exact (Likely.const L a).smul ih

variable {G:Gauge}{H:Source.Hol G}{d:ℕ}(σ:Survey G H d)(p:On.Grade G d)(c:Shade.Cut)

def spirit (q: PlaqAxes):Tile G:= fun x=> tie G (enter0 σ p) (V3 G (x,q))
lemma drama (a:ℝ): fuse σ p c a= mark1 σ p-∑ q:PlaqAxes,Shade.measure c a (spirit σ p q):=by
  unfold fuse engine; simp_rw [_root_.map_sum,Prelude.by_send]; congr! 1; apply Finset.sum_congr rfl; intro i _; rw [Prelude.sends]; rfl
abbrev bevel (a:ℝ):=overture d (fuse σ p c a)
def debit (a:ℝ):Stage G d d:= ⟨trunc coin d (bevel σ p c a), transported coin _ _⟩
lemma prime : ∃ n,∀ a,bevel σ p c a∈Load G d n:=by
  obtain ⟨n,h⟩:=cap_known coin (overture d (mark1 σ p)); refine ⟨max n ((d+4)*(1+d)), fun a=>?_⟩; unfold bevel; rw [drama,map_sub,_root_.map_sum]; refine Submodule.sub_mem _ (higher coin (le_max_left ..) h) (Submodule.sum_mem _ fun i _=> ?_); rw [Shade.quick_sum,map_sum]; apply Submodule.sum_mem; intro j _; rw [map_smul]; exact Submodule.smul_mem _ _ (higher coin (le_max_right ..) (recorder d (p:=spirit σ p i) (vetting σ p i) j)) -- uppercase P?
def diff (X:Stage G d d):= (trunc coin d) (X.val-cross (radial G d) X.val) -- but not enough? construct
lemma scaled_there (v:Cap G d)(a:ℝ)(L:Module.End ℝ (Hat G d))(h: ∀ c:ℝ,∀ v:Hat G d,L (orchestra d c v)=orchestra d c (L v)): cross L (scale a v)=scale a (cross L v):= sameCap fun X=>by rw [crossing,scaled,scaled,crossing,h]

def divide (u:Cap G d): Stage G d d:= ⟨trunc coin d u-cross (radial G d) (trunc coin d u),Submodule.sub_mem _ (transported coin _ _) (radial_keeps .. |>.symm ▸ transported coin (cross (radial G d) u) d)⟩
def middle (d:ℕ): Cap G d→ₗ[ℂ] Stage G d d where
  toFun:= divide
  map_add' a b:=by apply Subtype.ext; simp only [divide,map_add]; exact add_sub_add_comm ..
  map_smul' a b:=by apply Subtype.ext; simp only [divide,map_smul]; exact (smul_sub ..).symm
def stageLift (b:ℝ)(V:Stage G d d):Stage G d d:=⟨scale b V.val,capacity b V.property⟩

variable {ι: Type}{L:Filter ι} [L.IsCountablyGenerated]{a:ι→ℝ}(S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
include S he
set_option maxHeartbeats 400000 in
theorem compensatory : Still ℂ L fun i=> (tick a i d:ℂ) • stageLift (a i) (divide (bevel σ p c (a i))):=by
  obtain ⟨n,H⟩:=prime σ p c; let V (i:ι):Stage G d n:= tick a i d • (⟨scale (a i) (bevel σ p c (a i)), capacity _ (H _)⟩:Stage G d n)
  have ht (i): tick a i d • stageLift (a i) (divide (bevel σ p c (a i)))=middle d (V i).val := by
    set x:=tick a i d; let t:=a i; let u:=bevel σ p c t; change x • _=_; apply Subtype.ext; unfold V; rw [Submodule.coe_smul]; change x • scale t _= ((middle d) (x • scale t _)).val; rw [map_smul]; change x • scale t (trunc coin d u-cross _ (trunc coin d u))= x • (trunc _ _ (scale t _)- _); rw [map_sub, ← scaled_there (L:=radial G d) _ _ radial_saves, scale_trunc]
  simp_rw [ht]; let D: Stage G d n →ₗ[ℂ] Stage G d d:= middle d ∘ₗ (Load G d n).subtype
  apply redeem (fun v=>readStage v d) no_change; intro q
  let Z:= Hat G d × (Σ i:Fin (d+1), Litter.Stamp (i.val+1) G.Color)
  let f (z:Z): Module.Dual ℂ (Stage G d n):= (view z.1).toLinearMap ∘ₗ slide (gen z.2.1 z.2.2) ∘ₗ (Load G _ _).subtype; apply vouchers (f:=f) (g:=readStage q d ∘ₗ D) (p:=V)
  · intro x hx; have hh: cross (radial G d) x.val=x.val:= fade x.val fun v i X=> hx (show Z from (v,⟨i,X⟩)); change view q (trunc coin d x.val-cross _ _)=0; rw [radial_keeps,Submodule.subtype_apply,hh,sub_self,map_zero]
  intro z; change Likely L (fun i=> view z.1 (slide (gen z.2.1 z.2.2) ((V i).val))); simp_rw [V,Submodule.coe_smul,map_smul,bevel,elevated,echoes]; exact canyon z.2.2 σ c z.1 p S he

include p σ in
theorem fee_hint : By ℂ L (fun i=> (a i:ℂ) • (debit σ p c (a i))) 0 :=by
  apply redeemBy (fun v=> readStage v d) no_change; intro X; simp only [map_smul,map_zero]; change Tendsto (fun i=> (a i:ℂ) * view X (trunc coin d _)) L _; unfold bevel; simp_rw [drama,map_sub,_root_.map_sum,mul_sub, Finset.mul_sum]
  have hx:= ((Complex.continuous_ofReal.continuousAt.tendsto.comp S).mul_const (view X (trunc coin d (overture d (mark1 σ p))))).sub (tendsto_finsetSum (x:=L) (ι:=PlaqAxes) Finset.univ (fun i _=> Shade.steam c S he X (vetting σ p i))) -- change ν
  simp only [Function.comp_apply, Complex.ofReal_zero,zero_mul,Finset.sum_const_zero,sub_zero] at hx; exact hx
end YM.XSpace.Uptown
