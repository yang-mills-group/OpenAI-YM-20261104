import YM.MS.Halo.Mint
/-!
# Transport through physicists' signed-axis rotation in dimensional packets

Here prepare generic angular algebra for composition (using the existing extensive reflection
construction & individual Pilot/Spin operators in MS Arts). On legs the pilot beam action
is **right**: precompose by rotations. Will specialize to inverse for the convention on labels (frame rotations).
No global label basis assumed. Need preserve orientation at every point with regulator bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Weft
open Function Set Filter Finset
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Arts.Pilot MS.Koszul
open MS.Landau MS.Garment MS.Rock
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {A:Type}[Fintype A] [DecidableEq A]{m n:ℕ}{C:Type}[Fintype C] [DecidableEq C]
variable {G:Gauge}(s t:Spin A)
-- problem with Synth Simple.V.
omit [DecidableEq A] in
lemma pointS : (∀ p,s.turn p=t.turn p)→ s=t:=by intro he; cases s; cases t; congr; ext; exact congr_fun (he _) _

abbrev paste (s t:Spin A): Spin A:= ⟨t.turn.trans s.turn, fun p q=> Eq.trans (s.rad (t.turn p) (t.turn q)) (t.rad p q) ⟩
abbrev nil (A:Type)[Fintype A]: Spin A:= ⟨ContinuousLinearEquiv.refl .., fun _ _=>rfl ⟩
omit [DecidableEq A] in
lemma paste_t (p:Momentum A): (paste s t).turn p=s.turn (t.turn p):= rfl
local notation "Φ"=> Spin.leggo
local notation "Ε"=> Finset.univ
-- profile is transpose of matrix, composition reversed
lemma upper₀ (i j:A): (paste s t).profile i j=∑ l:A,t.profile i l*s.profile l j:= (s.orth (t.turn (spray i)) j).symm
lemma field_p (x y:Landau.Leg A C): (paste s t).prop x y=∑ l:Landau.Leg A C,t.prop x l*s.prop l y:= by
    simp only [Spin.prop, Spin.rayS,Fintype.sum_prod_type]; rcases x with ⟨⟨_|i,a⟩,c⟩ <;> rcases y with ⟨⟨_|j,b⟩,d⟩ <;> by_cases h:a=b <;> by_cases hx:c=d <;> simp [ Fintype.sum_option,h,hx,ite_mul,mul_ite, Spin.shadow,upper₀,Complex.ofReal_sum,Complex.ofReal_mul] -- recursion?
omit [Fintype C] in
lemma field_e (x y:Landau.Leg A C): (nil A).prop x y= if x=y then 1 else 0:= by
    rcases x with ⟨⟨_|i,a⟩,c⟩ <;> rcases y with ⟨⟨_|j,b⟩,d⟩ <;> by_cases h:a=b <;> by_cases hx:c=d <;> simp [ Spin.prop,h,hx,Spin.rayS,Spin.shadow, Spin.profile,spray,Pi.single_apply]; by_cases He:i=j <;> simp [He]; exact Ne.symm He -- tactic names on i if none fails

lemma beam_p (f:Row (Landau.Leg A C) (Momentum A) ℂ): (Spin.leggo C (paste s t)).beam f=(Φ C t).beam ((Φ C s).beam f):= by
    funext l; induction l generalizing f with| nil=> simp | cons a l ih=> rw [met,met]; simp_rw [served,map_sum,map_smul, Finset.sum_apply, Pi.smul_apply,smul_eq_mul ,ih ]; simp_rw [ show ∀ x, (Φ C (paste s t)).fieldC a.1 x=_ from fun x=> field_p s t a.1 x,Finset.mul_sum,Finset.sum_mul,mul_assoc ]; nth_rw 1 [Finset.sum_comm]; rfl
lemma beam_e (f:Row (Landau.Leg A C) (Momentum A) ℂ): (Φ C (nil A)).beam f=f:=by funext l; induction l generalizing f with| nil=> simp| cons a l ih=> simp_rw [met,ih, show ∀ x, (Φ C (nil A)).fieldC a.1 x=if a.1=x then 1 else 0 from fun _=>field_e _ _, ite_mul,one_mul,zero_mul]; simp; rfl
omit [DecidableEq A] in lemma undo : paste s.back s=nil A:= pointS _ _ fun _=> rear s
omit [DecidableEq A] in lemma undo' : paste s s.back=nil A:= pointS _ _ fun _=> front s
abbrev lamp (K:Spin (L m)) : Rack G m→ₗ[ℂ] Rack G m:= (flagS K G).beam
lemma beamL (X Y:Spin (L m))(u:Rack G m): lamp X (lamp Y u)=lamp (paste Y X) u:= (beam_p Y X u).symm
lemma beam_inv (X:Spin (L m))(u:Rack G m): lamp X (lamp X.back u)=u:= by rw [beamL,undo]; exact beam_e u
lemma beam_inv' (X:Spin (L m))(u:Rack G m): lamp X.back (lamp X u)=u:= by rw [beamL,undo']; exact beam_e u
-- arch decomposition by point with linear correction only on Left. simplifies all nested issues.
variable {k:ℕ}
lemma fuller (h:m≤n)(X:Spin (L m))(p: SectorP n): (arch h X).turn p=p+ Left h (X.turn (Cl h p)-Cl h p):= by
    rw [show (arch h X).turn p=_ from X.total h p ]; conv_rhs=> lhs; rw [← city h p ]
    rw [map_sub]; abel
lemma stack (p:k≤m)(q:m≤n)(X:Spin (L k)): arch q (arch p X)=arch (p.trans q) X:= by
 apply pointS; intro x; rw [fuller,fuller,fuller]; have hY: Cl p (Cl q x)=Cl (p.trans q) x:=rfl; rw [ hY, add_sub_cancel_left,show ∀ x, Left q (Left p x)=Left (p.trans q) x from fun x=> by rw [Left,Left,sons,rides_link] ]
lemma back_b (X:Spin (L m))(h:m≤n): arch h X.back=(arch h X).back:= by
 apply pointS; intro x; apply ( arch h X ).turn.injective; rw [front]; rw (occs:=.pos [1]) [← city h x]; rw [map_add,map_add,arch_identity,arch_identity,arch_on,arch_on,front,city h]
lemma arch_nil (h:m≤n): arch h (nil (L m))= nil (L n):= pointS _ _ (fun x=> by rw [fuller,show (nil (L m)).turn ( Cl h x )=Cl h x from rfl,sub_self,map_zero,add_zero]; rfl)
lemma selfA (X:Spin (L m)): arch (Nat.le_refl m) X=X:= by
 apply pointS; intro x; have he(x:SectorP m): Left (Nat.le_refl m) x=x:= funext fun i=> lasts (rises (Nat.le_refl m)) x i; nth_rw 1 [← he x]; rw [arch_on,he]
lemma arch_group (X Y:Spin (L m))(h:m≤n): arch h (paste X Y)=paste (arch h X) (arch h Y):= by
 apply pointS; intro x; rw [paste_t,← city h x]; simp_rw [map_add,arch_on,arch_identity]; rfl
-- commutation of any extension from prefix m with rotations acting only on others.
lemma commutes {K: Spin (L n)} (h:m≤n)(hv:∀ p,K.turn (Left h p)= Left h p)(X:Spin (L m)): paste (arch h X) K=paste K (arch h X):= by
 apply pointS; intro p; have H(a:SectorP n): Cl h (K.turn a)=Cl h a:= by
     funext i; change _= a (rises h i); change K.turn a (rises h i)=_; have he:=K.rad ( spray ( rises h i ) ) a; rw [fixedBasis h hv i] at he; simpa [ pairing,spray,Pi.single_apply,ite_mul ] using he
 rw [paste_t,paste_t,fuller,fuller,H,map_add,hv]
lemma strong (K: Spin Axis)(f:Mob G)(h:Sturdy false f): Sturdy false (fun n=> lamp (arch (Nat.zero_le n) K) (f n)) := by
 refine ⟨fun n X hX=>?_,fun {i j} he p=>?_⟩
 · rw [show (flagS X G).beam=_ from ( rfl : (flagS X G).beam=lamp X), beamL, commutes (Nat.zero_le n) (hX rfl),← beamL, (show lamp X (f n)= f n from h.turn n X hX) ]
 change ( flagS _ _ ).beam _ ( Arts.lift _ _) = _; -- shadow h
 rw [ ← stack (Nat.zero_le i) he K, Spin.telescopeS ]; rw [funext fun k=> h.grows he k]
end YM.FVA2.Position.Weft
