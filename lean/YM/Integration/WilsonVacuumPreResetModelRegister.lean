import YM.Integration.WilsonVacuumPreResetCurvatureRack
import YM.RG01Estimate.GreenEye

/-! A single original address list for signed kinetic and covering
corrections. Appending the regular catalogue keeps the original hard list. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetModelRegister
open Lattice RG Wilson PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open Push Push.AbsoluteSums Collection Quotes Song Meadow RG01Estimate RG01Estimate.Precise
open Push.AbsoluteSums.Animals ConnectedActivityE6 Next.Scheduling Extra.Iteration WilsonStartup Geo
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def joined (A B:Leads G n):Leads G n:=
  ⟨Caddy.stores A.listing B.listing.reg,Caddy.insertP B.trunk A.trunk,
    Caddy.insertP B.pioneers A.pioneers,A.bill+B.bill⟩

private theorem split (f g f' g':ℕ→ Config G n→ℝ):
    Caddy.insertP f g-Caddy.insertP f' g'=Caddy.insertP (f-f') (g-g') ∧
    -(Caddy.insertP f g-Caddy.insertP f' g')=Caddy.insertP (-(f-f')) (-(g-g')):=by
  constructor
  all_goals funext i;obtain ⟨j,rfl⟩:=Caddy.e.symm.surjective i;cases j <;> simp [Caddy.insertP,Function.comp_apply]

private theorem mirrors {A:Listing G n}{B:ℕ→RegularAddress n}{f g:ℕ→ Config G n→ℝ}
    {s:Signed}{b:Site n}(x:Caddy.Mirrors A.reg s b f)(y:Caddy.Mirrors B s b g):
    Nonempty (Caddy.Mirrors (Caddy.stores A B).reg s b (Caddy.insertP g f)):=by
  let p:=Equiv.sumCongr x.walks y.walks
  let w:Equiv.Perm ℕ:=(Caddy.e.trans p).trans Caddy.e.symm
  have eq (i:ℕ):Caddy.e (w i)=p (Caddy.e i):=Caddy.e.apply_symm_apply _
  refine ⟨⟨w,?_,?_,?_⟩⟩
  · intro i
    change (Sum.elim A.reg B (Caddy.e (w i))).site=affine s b (Sum.elim A.reg B (Caddy.e i)).site
    rw [eq]
    cases j:Caddy.e i with
    | inl k=>exact x.hooks k
    | inr k=>exact y.hooks k
  · intro i
    change (Sum.elim A.reg B (Caddy.e (w i))).support=(Sum.elim A.reg B (Caddy.e i)).support.image (affine s b)
    rw [eq]
    cases j:Caddy.e i with
    | inl k=>exact x.hues k
    | inr k=>exact y.hues k
  · intro i
    change Sum.elim f g (Caddy.e (w i))=Sum.elim f g (Caddy.e i) ∘ pull s b
    rw [eq]
    cases j:Caddy.e i with
    | inl k=>exact x.posts k
    | inr k=>exact y.posts k

theorem purchased (T:BudgetPoint)(A B:Leads G n){e e' w w':ℝ}
    (a:Suggests T A e w)(b:Suggests T B e' w'):
    Suggests T (joined A B) (e+e') (w+w'):=by
  refine ⟨Caddy.posting_bounds _ _ _ a.live b.live,Caddy.posting_bounds _ _ _ a.asking b.asking,?_,?_⟩
  · change Meadow.Budget T (Caddy.stores A.listing B.listing.reg).reg
      (Caddy.insertP B.trunk A.trunk-Caddy.insertP B.pioneers A.pioneers) _
    rw [(split ..).1]
    exact Caddy.posting_bounds _ _ _ a.extra b.extra
  intro s c
  obtain ⟨⟨a₁⟩,⟨a₂⟩,⟨a₃⟩⟩:=a.mirror s c
  obtain ⟨⟨b₁⟩,⟨b₂⟩,⟨b₃⟩⟩:=b.mirror s c
  refine ⟨mirrors a₁ b₁,mirrors a₂ b₂,?_⟩
  change Nonempty (Caddy.Mirrors _ s c (-(Caddy.insertP B.trunk A.trunk-Caddy.insertP B.pioneers A.pioneers)))
  rw [(split ..).2]
  exact mirrors a₃ b₃

private def widen {A:Listing G n}{u:ℕ→ Config G n→ℝ}{r q:ℕ}(h:r≤q)(X:Abacus.Rack A r u):Abacus.Rack A q u where
  atW:=X.atW
  seat:=X.seat
  bound:=X.bound
  sums:=X.sums
  paid:=X.paid
  priced i hi x hx _ hy:=(neighbors_mem ..).2 (((neighbors_mem ..).1 (X.priced i hi x hx hy)).trans h)

private def reverse {A:Listing G n}{u:ℕ→ Config G n→ℝ}{r:ℕ}(X:Abacus.Rack A r u):Abacus.Rack A r (-u) where
  atW:=X.atW
  seat:=X.seat
  bound i hi:=by change -u i=0;rw [X.bound i hi,neg_zero]
  sums:=X.sums
  paid:=X.paid
  priced:=X.priced

theorem assembled (A B:Leads G n){s t r:ℕ}(hs:s≤r)(ht:t≤r)(x:Abacus.Rack A.listing s A.pioneers)
    (y:Abacus.Rack B.listing t B.pioneers):
    ∃z:Abacus.Rack (joined A B).listing r (joined A B).pioneers,z.polygon=x.polygon+y.polygon:=by
  let X:=widen hs x
  let Y:=reverse (widen ht y)
  have negation:Y.polygon=-y.polygon:=by
    funext j U
    simp [Y,reverse,widen,Abacus.Rack.polygon,Pi.smul_apply,smul_neg]
  have h:∃z:Abacus.Rack (Caddy.stores A.listing B.listing.reg) r
      (Caddy.insertP (-(-B.pioneers)) A.pioneers),z.polygon=x.polygon+y.polygon:=by
    refine ⟨Caddy.signedR A.listing X Y,?_⟩
    rw [Caddy.pacts,negation,sub_neg_eq_add]
    rfl
  rw [neg_neg B.pioneers] at h
  exact h

end YM.Integration.WilsonVacuumPreResetModelRegister
