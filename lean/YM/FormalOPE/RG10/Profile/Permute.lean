import YM.Contact.JacobiAction
import YM.FormalOPE.RG10.Profile.Law
/-!
# Label permutation, opening and delivery by real formal gathers.
Markers distinguish equal labels everywhere. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
    Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
    InversionTop LatticePT Lattice Grid FlatFeed RG10.Position RG10.Position.Grade
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{n d:ℕ}(r:Equiv.Perm (Fin n))(t:Test n)
local notation "h" => Contacts.permuteList r
private theorem restore (f:Test n): tsupport (f ∘ (Contacts.permuteList r).symm) = h '' tsupport f := by
 rw [show tsupport (f ∘ (Contacts.permuteList r).symm) = (Contacts.permuteList r).symm ⁻¹' _ from tsupport_comp_eq_preimage f (Contacts.permuteList r).symm.toHomeomorph]
 ext p; constructor; intro hp; exact ⟨_, hp, (Contacts.permuteList r).apply_symm_apply _⟩; rintro ⟨x,hx,rfl⟩; simpa only [Set.mem_preimage, LinearIsometryEquiv.symm_apply_apply]

def remark : Test n := ⟨t ∘ (Contacts.permuteList r).symm,t.contDiff.comp (Contacts.permuteList r).symm.toContinuousLinearEquiv.contDiff,
   by rw [HasCompactSupport,restore]; exact t.hasCompactSupport.image (Contacts.permuteList r).continuous,fun x hx=>by rw [restore] at hx; obtain ⟨x,hx,rfl⟩:=hx; exact Points.rearrange_in r (t.tsupport_subset hx)⟩
lemma remark_at (x:Points n) : remark r t (Points.rearrange r x)=t x:= show t ((Contacts.permuteList r).symm (h x))=_ from congr_arg t ((Contacts.permuteList r).symm_apply_apply _)

variable (P : Plan F)(q:ℕ+)(m:ℕ)(u:Fin n→ Deck F d)
lemma nodeNatural (x:Grid.offsets q n m)(i:ℕ) : nodes P q m i (u ∘ r) (x ∘ r)=nodes P q m i u x := by
 have he (z:Native q m) : mesh P q m (u ∘ r) (x ∘ r) z=mesh P q m u x z:= by
   let g:=InversionTop.feed (G:=G) (side_even q m); let f:= g.step (InversionTop.vertices G (LatticePT.side q m)); exact congr_arg f (Equiv.prod_comp r (fun i=> membrane P.H P.source P.sound P.chosen P.liftOff (Deck.token F d (u i)) (x i+z) (epsilon q m)))
 unfold nodes; simp_rw [he]
private abbrev renumber (U:Type*) := Equiv.arrowCongr r.symm (Equiv.refl U)
lemma beginNatural : P.begins q m d (task (remark r t) (u ∘ r))= P.begins q m d (task t u) := by
 ext i:1; rw [bill,bill]; rw [← Equiv.sum_comp (renumber r (Native q m))]; apply sum_congr rfl; intro k _; change (remark r t _).re * nodes _ _ _ _ _ (k ∘ r)=_
 rw [nodeNatural,show Grid.sample q m ((renumber r (Native q m)) k)=Points.rearrange r (Grid.sample q m k) from rfl,remark_at]
lemma insertNatural {V: Type*}[Fintype V](B:Mark V PertExtension.Physical.Profile.n→fps)(T:FrameAt V fps)(u: Fin n→ V)(he : ∀ v:Fin n→V,B (task (remark r t) (v ∘ r))= B (task t v)) :
    PertExtension.Position.insert V _ B T (task (remark r t) (u ∘ r)) = PertExtension.Position.insert V _ B T (task t u) := by
 change ∑ v:Fin n→ V,B (task (remark r t) v)*∏ i,T (u (r i)) (v i)= ∑ v:Fin n→ V,B (task t v)*∏ i,T (u i) (v i); rw [← Equiv.sum_comp (renumber r V)]; apply sum_congr rfl; intro i _; change B (task _ (i∘r))*_= _; rw [he]; exact congr_arg _ (Equiv.prod_comp r (fun j=>T (u j) (i j)))
lemma countedNatural : Plan.collect F P q m d (task (remark r t) (u ∘ r)) = Plan.collect F P q m d (task t u) := by
 exact congr_arg (Peal.Xaction F (P.dressed q m 6)) (show P.dressed q m d _=P.dressed q m d _ from insertNatural r t _ (P.poses q m d) u (beginNatural r t P q m))
variable {P} {Y:Drivers}(Z:Patience P Y)
lemma posed : Z.Yield (task (remark r t) (u ∘ r))= Z.Yield (task t u) := by
 refine Drivers.Credit.accepts (x:=fun q i=> Plan.collect F P q i d (task t u)) ?_ (Z.collected _)
 have he:= Z.collected (task (remark r t) (u ∘ r)); simp_rw [countedNatural] at he; exact he
lemma scaled (R: Rails F) : R.adjust Z d (task (remark r t) (u ∘ r)) = R.adjust Z d (task t u) :=
 insertNatural _ _ _ _ _ (fun x=> posed r t x Z)
end YM.FormalOPE.RG10.Profile
