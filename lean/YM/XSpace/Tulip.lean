import YM.XSpace.Tabloid
/-! # Power stakes with translated anchors -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gland
open Function Set Filter Lattice Chart2 MvPolynomial Trace Outline Relief Mu Tide Chiral Litter Extra.FD Finsupp Pages Next.Rank.Normal Next.Rank.Beamer
open scoped Topology BigOperators Pointwise
variable {G:Gauge} {n k i j:ℕ}
local notation "U" => UnitIndex G
abbrev Levee (G:Gauge):= Submodule ℂ (Mu.Stamp G)
def stem (G:Gauge)(i:ℕ): Levee G:= Submodule.span ℂ (harp '' (cane i G : Set (Line G)))
def Duo (G:Gauge)(i j:ℕ):= stem G i * stem G j
def Trio (G:Gauge)(i j k:ℕ):= Duo G i j * stem G k
variable {x:Mu.Stamp G}
lemma sap {x: Line G}(h:x∈cane i G): harp x ∈ stem G i:=Submodule.subset_span ⟨x,h,rfl⟩
lemma through (S:Levee G)(h:∀ x∈cane i G,∀ y∈cane j G,harp x*harp y∈ S): Duo G i j ≤S:=by
  unfold Duo stem; rw [Submodule.span_mul_span]; apply Submodule.span_le.mpr; rintro p ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩; exact h x hx y hy
lemma through3 (S:Levee G)(h:∀ x∈cane i G,∀ y∈cane j G,∀ z∈cane k G,harp x*harp y*harp z∈ S): Trio G i j k ≤ S:=by
  unfold Trio Duo stem; simp_rw [Submodule.span_mul_span]; apply Submodule.span_le.mpr; rintro p ⟨_,⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩,_,⟨z,hz,rfl⟩,rfl⟩; exact h x hx y hy z hz
lemma cane_move {x:Line G}(h:x∈cane i G)(y:Cover): displace y x∈cane i G:=by
  induction h using Submodule.span_induction with | mem x h=> obtain ⟨p,rfl⟩:=h; unfold Rudder.worth; rw [toll,pin]; exact Submodule.subset_span ⟨{p with head:=radius y p.head},rfl⟩| zero=> rw [map_zero]; exact Submodule.zero_mem _| add _ _ _ _ h h'=> rw [_root_.map_add]; exact Submodule.add_mem _ h h'| smul _ _ _ h=>rw [_root_.map_smul]; exact Submodule.smul_mem _ _ h
lemma k₁ : stem G i ≤ stem G 0:= Submodule.span_le.mpr (by rintro p ⟨x,h,rfl⟩; exact sap (Trace.tariff x))
lemma k₂ : Duo G i j ≤ Duo G 0 0:= mul_le_mul' k₁ k₁
lemma k₃ : Trio G i j k ≤ Trio G 0 0 0:= mul_le_mul' k₂ k₁
lemma duo_swap : Duo G i j= Duo G j i:=mul_comm ..
lemma trio3 : Trio G i j k=stem G i*(stem G j*stem G k):=mul_assoc ..
lemma k₂g : Duo G i j ≤ Pages.rank 2 _:= through _ fun _ _ _ _=> (strongs ..).mul (strongs ..)
lemma k₃g : Trio G i j k ≤ Pages.rank 3 _:= through3 _ fun x _ y _ z _=> ((strongs ..).mul (strongs ..)).mul (strongs ..)
lemma lost (s:UnitIndex G): X s∈stem G 0:=by rw [← harps]; exact sap (Trace.tariff _)
lemma staked_s (a:U→₀ℕ)(c:ℂ):monomial a c∈ stem G 0 ^ Volume a:=by
  apply Extra.FD.per_factor a; rw [show Volume (0:U→₀ℕ)=0 from map_zero _,pow_zero]; change C c∈_; rw [← mul_one (C c), C_mul']; exact Submodule.smul_mem _ _ (Submodule.mem_one.mpr ⟨1,map_one (algebraMap ℂ _)⟩)
  intro u i h; rw [monomial_add_single,pow_one, volume_fee, pow_succ]; exact Submodule.mul_mem_mul h (lost i)
lemma staked {p:Stamp G}(h:Hom p n): p∈ stem G 0 ^ n:= by rw [p.as_sum]; refine Submodule.sum_mem _ fun c hc=>?_ ; exact (h (MvPolynomial.mem_support_iff.mp hc)) ▸ staked_s c _
lemma stake (h:Pages.Hom x 2): x∈ Duo G 0 0:= by simpa only [pow_two,Duo] using staked h
lemma security (h:Pages.Hom x 3):x∈ Trio G 0 0 0:= by simpa only [Trio,Duo,pow_succ,pow_zero,one_mul] using staked h
-- compress to value of potential at root (for local shifts)
local notation "A(" u "," i "," a ")" => X (R:=ℂ) (σ:= UnitIndex G) ((u,i),a)
def compress (G:Gauge) : Stamp G→ₐ[ℂ] Stamp G:= rename fun i:UnitIndex G=>(((0:Cover),i.1.2),i.2)
lemma compress_at (X:Contact G)(p:Stamp G): pit X (compress G p)=pit (fun i:Edge Cover=> X ((0:Cover),i.2)) p:=by suffices hx : (pit X).comp (compress G)=_ from DFunLike.congr_fun hx p; apply algHom_ext; intro k; rw [AlgHom.comp_apply,compress,rename_X,pit,pit,aeval_X,aeval_X];rfl
private lemma stem_diff (x:Cover)(t i: Axis)(a:G.ColorIndex): A(x+step t,i,a)-A(x,i,a)∈stem G 1:=by
  let z:U:=((x,i),a); let y:=needle z; have h:=sap (gated z [t]); have he:gate [t] y =needle ((x+step t,i),a)-y:= by change displace (step t) y-y=_; unfold y z; rw [pin,radius]; rw [add_comm x (step t)]
  suffices harp (gate [t] y)= A(x+step t,i,a)-A(x,i,a) by rw [← this]; exact h
  rw [he]; unfold harp y; rw [map_sub,map_sub]; exact congrArg₂ _ (harps _) (harps _)
lemma homework (s:UnitIndex G): X s-compress G (X s)∈stem G 1:=by
  obtain ⟨⟨x,i⟩,a⟩:=s; rw [compress,rename_X]; change A(x,i,a)-A(0,i,a)∈ _; generalize h:street x=n; induction n generalizing x with
  | zero=> obtain hh|⟨y,hy,_⟩:=past_stepping x; · rw [hh,sub_self]; exact Submodule.zero_mem _
           omega
  | succ n ih=> obtain hh|⟨y,hy,H,t,ht⟩:=past_stepping x; · rw [hh,sub_self]; exact Submodule.zero_mem _
                rw [← sub_add_sub_cancel _ (A(y,i,a)) _]; refine Submodule.add_mem _ ?_ (ih y (by omega)); rcases ht with h|h; rw [h]; apply stem_diff; rw [h,← neg_sub]; exact Submodule.neg_mem _ (stem_diff x t i a)
-- pivotal theorem: highest slots lift the anchored difference with one precise power
lemma hollow (h:Hom x 2): x-compress G x∈ Duo G 1 0:=by
  have ht(s:U→₀ℕ)(k:ℂ):Volume s=2 → monomial s k-compress G (monomial s k)∈ Duo G 1 0:=by
    apply Extra.FD.per_factor s; simp; intro v j H hh; obtain ⟨i,rfl⟩:= rank1_support v (by rw [volume_fee] at hh; omega); rw [monomial_add_single,pow_one,monomial_single_one, mul_assoc (C _),C_mul', map_smul,← smul_sub,map_mul]
    let u:=X (R:=ℂ) i; let w:= X (R:=ℂ) j; set p:=compress G u; have hp:p∈stem G 0:=by unfold p compress u; rw [rename_X]; apply lost
    apply Submodule.smul_mem; rw [show u*w-p*compress G w = (u-p)*w+(w-compress G w)*p from by ring]; exact Submodule.add_mem _ (Submodule.mul_mem_mul (homework i) (lost j)) (Submodule.mul_mem_mul (homework j) hp)
  rw [x.as_sum,map_sum,← Finset.sum_sub_distrib]; exact Submodule.sum_mem _ (fun c hc=> ht c _ (h (MvPolynomial.mem_support_iff.mp hc)))
end YM.XSpace.Gland
