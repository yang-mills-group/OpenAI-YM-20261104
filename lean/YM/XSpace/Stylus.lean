import YM.XSpace.Concord
import YM.XSpace.Removal

/-!
# Propagate against straight linear mark charges on the cover

Real coordinates (vertices/counterterms may still be complex linear). Restore
complex Gaussian covariance in contractions via `waver`. Exact K D=L identity
on gauge-null tests. All statements at unit spacing unless noted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Trace
open Scale Lattice Sail Litter Chart2 Further.FreeCovariance.KP Function Filter Finsupp MvPolynomial Outline Next.Rank.Normal
open scoped Topology BigOperators ContDiff
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F] {G:Gauge}

def lamp : Module.End ℝ (Cover→F):= ∑ i:Axis,rat i ∘ₗ teeth i
lemma lamp_at (p: Cover→F)(x:Cover):lamp p x=∑ i:Axis,(p x-p (x+step i)+(p x-p (x-step i))):=by unfold lamp; rw [LinearMap.sum_apply,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; change p (_-_+_) - _-(_-_)=_; rw [sub_add_cancel]; change p x-p (x-step i)-(p (x+step i)-p x)=_; abel
lemma poisson (x:Cover): lamp cover x=if x=0 then 1 else 0:=by
  let n:= Top.side; let K (p:ℕ)(x:Cover):=Potential.G (n p) (wrap (n p) x)
  have hx (x:Cover): Tendsto (fun i=> K i x) atTop (𝓝 (cover x)):= by
    have he:= (Complex.continuous_re.tendsto _).comp (toward [] Top.side Top.grows x); simp_rw [seen_bare] at he; exact he
  have he : Tendsto (fun i=>lamp (K i) x) atTop (𝓝 (lamp cover x)):=by simp_rw [lamp_at]; exact tendsto_finsetSum _ fun i _=> ((hx x).sub (hx _)).add ((hx x).sub (hx _))
  apply tendsto_nhds_unique he
  let d:ℝ:= if x=0 then 1 else 0
  let g p:= (((n p).val:ℝ)^4)⁻¹
  have h : Tendsto g atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α:=ℝ) (n:=4) (by decide)).comp (tendsto_natCast_atTop_atTop.comp Top.grows))
  have hi:= (show Tendsto (fun _:ℕ=> d) atTop (𝓝 d) from tendsto_const_nhds).sub h; rw [sub_zero] at hi; refine hi.congr' ?_
  filter_upwards [Top.grows.eventually_gt_atTop (2*reach x)] with i hi; change d-g i=_; rw [lamp_at]; unfold K; simp_rw [map_add,map_sub,wrap_step]; rw [← Potential.scalar_at, Potential.poisson]; unfold g d; congr 1; congr 1
  rw [← map_zero (wrap (n i)),Set.InjOn.eq_iff (wrap_injOn (n i)) (show ∀ j, -((n i).val:ℤ) < 2*x j∧ 2*x j ≤ (n i).val from fun j=>by have he:=reach_at x j; unfold n;omega) (show ∀ j:Axis,-((n i).val:ℤ)< 2*((0:Cover) j)∧ 2*((0:Cover) j) ≤ (n i).val from fun j=>by simp)]

lemma cover_even (x:Cover) : cover (-x)=cover x:= by
  have hx:= Sail.toward [] Top.side Top.grows x; have hh:= Sail.toward [] Top.side Top.grows (-x); have p(n:Side): Sail.seen [] n (-x)= Sail.seen [] n x:=by rw [Sail.seen_bare,Sail.seen_bare,map_neg,Potential.even]
  exact congr_arg Complex.re (tendsto_nhds_unique (hh.congr fun i=> p (Top.side i)) hx)
lemma reciprocity (x y: Cover): cover (x-y)=cover (y-x):= by rw [← neg_sub y,cover_even]

abbrev UnitIndex (G:Gauge):=Bone G ℤ
abbrev Line (G:Gauge):=UnitIndex G→₀ ℝ
abbrev Contact (G:Gauge):=Tape G.Color

def ram : UnitIndex G→Module.Dual ℝ (Contact G):=fun x=> (EuclideanSpace.proj x.2).toLinearMap ∘ₗ LinearMap.proj x.1
lemma ram_at (x:UnitIndex G)(A:Contact G):ram x A=A x.1 x.2:=rfl
def probe : Line G →ₗ[ℝ] Module.Dual ℝ (Contact G):= linearCombination ℝ ram
def needle (p:UnitIndex G):= Finsupp.single p (1:ℝ)
lemma sift (p:UnitIndex G)(x:ℝ):probe (Finsupp.single p x)=x • ram p:=by rw [probe,linearCombination_single]
lemma probes (p:UnitIndex G):probe (needle p)=ram p:=by rw [needle,sift,one_smul]

def crumb (i:UnitIndex G):Contact G:= Pi.single i.1 (basisC G i.2)
def bead (u v:UnitIndex G):ℝ:=if u.1.2=v.1.2∧ u.2=v.2 then cover (u.1.1-v.1.1) else 0
def φ (x:UnitIndex G): Contact G:= fun e=> if x.1.2=e.2 then cover (e.1-x.1.1) • basisC G x.2 else 0
lemma dotter (u v:UnitIndex G):ram u (crumb v)=if u=v then 1 else 0:=by rw [ram_at,crumb]; by_cases h:u.1=v.1; rw [h,Pi.single_eq_same]; simp [Prod.ext_iff,h]; rw [Pi.single_eq_of_ne h]; simp [Prod.ext_iff,h]
lemma rot (u v:UnitIndex G):ram u (φ v)= bead u v:=by rw [ram_at,φ]; by_cases h:u.1.2=v.1.2; rw [if_pos h.symm]; simp only [bead, h, true_and,PiLp.smul_apply,smul_eq_mul]; simp; split_ifs <;> simp_all; simp [bead,h]
lemma beaded (u v:UnitIndex G): (↑(bead u v):ℂ)= (duskCov G).cov u v:=by change _=coal _ _ _; unfold bead coal; split <;> simp_all [reciprocity u.1.1]
lemma beads (u v:UnitIndex G): bead u v=bead v u:= by apply Complex.ofReal_injective; rw [beaded,beaded]; apply (duskCov G).symm

def deposit : Line G→ₗ[ℝ] Contact G:= linearCombination ℝ crumb
def bake : Line G→ₗ[ℝ] Contact G:= linearCombination ℝ φ
lemma deposited (p:UnitIndex G):deposit (needle p)=crumb p:=by rw [deposit,needle,linearCombination_single,one_smul]
lemma baked (p:UnitIndex G):bake (needle p)=φ p:=by rw [bake,needle,linearCombination_single,one_smul]
lemma line_eq {M : Type*}[AddCommMonoid M][Module ℝ M]{A B:Line G→ₗ[ℝ]M}(h:∀ p:UnitIndex G,A (needle p)= B (needle p)):A=B:=by
  apply Finsupp.lhom_ext; intro a m; have he : Finsupp.single a m=m • needle a:=by simp [needle]
  rw [he,map_smul,map_smul,h]

def divine : Tape F→ₗ[ℝ] (Cover→F):= ∑ i:Axis,rat i ∘ₗ twig i
lemma job_parts (A:Tape F) (i:Axis):twig i (press A)= lamp (twig i A)-teeth i (divine A):=by
  have he (i j:Axis)(p:Cover→F): teeth i (rat j p)= rat j (teeth i p):=by funext x; change p (x+step i-step j)- _-(_-_) = p (x-step j+step i) - _-(_-_); rw [show x+step i-step j=x-step j+step i by abel]; change _-(p (x+step i)) -(p (x-step j)-p x)= _-p (x-step j)-(p (x+step i)-p x); abel
  unfold divine lamp; rw [job,LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; simp only [LinearMap.comp_apply, he]; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _=>map_sub (rat j) (teeth j (twig i A)) (teeth i (twig j A))
lemma fit_value (x:Cover)(A: Tape F)(i:Axis):twig i A x=A (x,i):=rfl
lemma basis_heat (c:UnitIndex G)(k:Axis):lamp (twig k (φ c))=twig k (crumb c):=by
  funext x; rw [lamp_at]; unfold crumb; simp only [fit_value,φ]; by_cases h:k=c.1.2
  · simp_rw [if_pos h.symm,← sub_smul,← add_smul]; rw [← Finset.sum_smul]; have he:= poisson (x-c.1.1); rw [lamp_at] at he; simp_rw [show ∀ j:Axis, x+step j-c.1.1=x-c.1.1+step j from fun j=>by abel,show ∀ j:Axis,x-step j-c.1.1=x-c.1.1-step j from fun j=>by abel]; rw [he]
    by_cases p:x=c.1.1; simp [p,h]; simp [ Prod.ext_iff, p,sub_ne_zero.mpr p]
  have he : (x,k)≠c.1:=by rw [ne_eq,Prod.ext_iff]; exact fun p=> h p.2
  simp [Ne.symm h,he]
lemma smolt (A:Line G)(i:Axis): lamp (twig i (bake A))=twig i (deposit A):=by suffices h : lamp ∘ₗ twig i ∘ₗ (bake (G:=G))= twig i ∘ₗ deposit from LinearMap.congr_fun h A; apply line_eq; intro x; simp only [LinearMap.comp_apply,baked, deposited, basis_heat]
private def palm (x:Cover)(i:G.ColorIndex)(p:Cover): G.Color:= cover (x-p) • basisC G i
lemma color_equalizer (x y:G.ColorIndex) (r:ℝ): (r • basisC G x) y= if x=y then r else 0:= by simp [eq_comm,mul_ite]
private lemma stem_basis (c:UnitIndex G)(x:Cover)(j:G.ColorIndex):divine (φ c) x j= ram c (stream (palm x j)):=by
  unfold divine; rw [LinearMap.sum_apply]; change (EuclideanSpace.proj j) ((∑ i:Axis,(rat i ∘ₗ twig i) (φ c)) x)= _; rw [Finset.sum_apply,map_sum, Finset.sum_eq_single c.1.2]
  · change (φ c (x-step c.1.2,_) - φ c (x,c.1.2)) j=(palm x j (c.1.1+step c.1.2)-palm x j c.1.1) c.2; simp only [φ,palm,if_true,PiLp.sub_apply,color_equalizer]; rw [show x-(c.1.1+step c.1.2)=x-step c.1.2-c.1.1 by abel]; simp [eq_comm]
  · intro i _ hi; change (φ c (x-step i,i)-φ c (x,i)) j=0; simp [φ,Ne.symm hi]
  simp
lemma electric (A:Line G)(x:Cover)(j:G.ColorIndex) : divine (bake A) x j=probe A (stream (palm x j)):=by
  let v: Contact G:= stream (palm x j); let f: Line G→ₗ[ℝ] ℝ:= (EuclideanSpace.proj j).toLinearMap ∘ₗ LinearMap.proj x ∘ₗ divine ∘ₗ bake; change f A=probe.flip v A; suffices f=probe.flip v from this ▸ rfl; apply line_eq; intro i; change divine (F:=G.Color) _ _ j= probe (needle i) v; rw [baked,probes]; exact stem_basis ..
def Stops (u:Line G): Prop:= ∀ p:Cover→G.Color, probe u (stream p)=0
theorem reverts (A: Line G)(h:Stops A): press (bake A)=deposit A:=by
  have he : divine (bake A)=0:=by ext x j; rw [electric]; exact h ..
  funext i; obtain ⟨i,j⟩:=i; rw [← fit_value _ (press _) j, ← fit_value _ (deposit A) j,job_parts, smolt,he,map_zero,sub_zero]
end YM.XSpace.Trace
