import YM.X.Grow.Output
import YM.PertExtension.Ticked
/-!
# Top-symbol EXACT restore on the K-Tower. Non-perfected: retains ∗higher∗ weight in ordinary evaluation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Grow
open MvPolynomial Function Lattice Next.Rank Normal LiftMark Maxwell Maxwell.Free Finset Reed
open Stems (Pin Hair Curly Brush arc blade com) -- Fan namespace Reed open above
open PertExtension LatticePT Next.Rank.Beamer Next.Rank.Configuration
open scoped Topology Classical Pointwise
variable {G:Gauge} {V W I:Type*} {u:V→ℕ}{n m k d:ℕ}

abbrev Film (G:Gauge) (n:ℕ):= (KeyIn G n)⊕ Atom G
local notation "Φ"=> (vapor G)
def postP (n:ℕ)(i:Film G n): Fan G:= Reed.optic Heat.Ray.address n i
def assignP (n:ℕ): poly (Film G n)→ₐ[ℂ] Curly G:= exchange (com ∘ postP n)
lemma assign_post {n:ℕ}(i:Film G n): assignP n (MvPolynomial.X i)= glyph (com (postP n i)):= Normal.exchange_x ..
lemma light {n:ℕ}(p:poly (Atom G)) : assignP n (exchange (features n Heat.Ray.address 1) p)= Stems.loom p:=by
     apply DFunLike.congr_fun (f:=(assignP n).comp (exchange (features n Heat.Ray.address 1))); ext1 i
     apply Stems.snap_ext; intro s; rw [AlgHom.comp_apply,exchange_x,Stems.loom,exchange_x];
     let C:=features n Heat.Ray.address 1 i; 
     let L:= ((Stems.snap s).comp (assignP n)).toLinearMap
     change L (Finsupp.linearCombination ℂ _ C)= Stems.snap s _; rw [LinearMap.map_finsupp_linearCombination]; have he(j: Film G n): L (MvPolynomial.X j)= (↑(passcode Heat.Ray.address 1 n j (advert s)):ℂ):= by change Stems.snap s (assignP n _) = _; rw [assign_post,Stems.com_text,Stems.snaps_blade]; exact congr_arg Complex.ofReal (sees Heat.Ray.address n j s)
     change Finsupp.linearCombination ℂ (fun j:Film G n=> L (MvPolynomial.X j)) C= Stems.snap s _; simp_rw [he]; unfold C; rw [proves n Heat.Ray.address 1 zero_lt_one,comp_apply,Stems.com_text,Stems.snaps_blade]; apply congr_arg
     exact (arc_flat (A:=s) (Heat.Ray.address i)).symm

def world (n:ℕ) (X:Word G):poly (Film G n):= exchange (features n Heat.Ray.address 1) (Vertex.normalized X.S X.H X.sound X.chosen X.axis)
def looking (X:Word G): Curly G:= Stems.loom (Vertex.normalized X.S X.H X.sound X.chosen X.axis)
def labelledP (X:Word G): Labels.Label G X.d:= X.F.basis X.axis
lemma loom_eq (n:ℕ)(X:Word G): assignP n (world n X) = looking X:= light _
lemma pureR (X:Word G): MvPolynomial.IsWeightedHomogeneous Labels.generation (labelledP X).val X.d:= by
     have h := Labels.pure_grade _ _|>.mp (X.F.pure X.axis); intro a ha; have hh:=h ha; rw [Labels.weight_slot] at hh; exact (congr_arg Prod.fst hh).trans X.weight
lemma restored (X:Word G)(h:X.d≤d): level bear X.d (world d X)=rename Sum.inl (thawKey (Labels.raiseLabel G h (labelledP X))) := Vertex.priced .. -- inspect
lemma thaws {X:Labels.Label G d} (hp:IsWeightedHomogeneous Labels.generation X.val n) : IsWeightedHomogeneous (LiftMark.key G d) (thawKey X) n:= by
     apply hom_feed (p:=X.val) (boundKey G d) ?_ hp; intro i; rw [boundKey,MvPolynomial.aeval_X]; split
     · exact isWeightedHomogeneous_X ..
     exact isWeightedHomogeneous_zero ..
lemma strong_world (X:Word G)(h:X.d≤d) : Strong bear X.d (world d X):= by
     have hp := thaws (X:=Labels.raiseLabel G h (labelledP X)) (pureR X); have h₁ : Strong bear X.d (level bear X.d (world d X)) := by rw [restored X h]; apply Strong.of_pure; refine hom_feed (rename Sum.inl) ?_ hp; intro i; rw [rename_X]; exact isWeightedHomogeneous_X ..
     let A:=world d X; let p:=level bear X.d A; change Strong bear X.d A; exact (sub_add_cancel A p) ▸ (((Strong.after (w:=bear) A X.d).weaken (by omega)).add h₁)

abbrev realSign (i:Labels.Key G) := ((Labels.axes G i.1).coord i.2).comp Maxwell.gaugeJet

def layBox : Labels.Pol G→ₐ[ℂ] Book G:= MvPolynomial.aeval fun i:Labels.Key G=> colorL (i.1+1) ((realSign i) ∘ₗ (shelve i.1))
lemma layBox_test (x:Long G)(p:Labels.Pol G): probeL x (layBox p)=Labels.read (fun n=> gaugeJet (shelve n (x (n+1)))) p:= by apply DFunLike.congr_fun (f:=(probeL x).comp layBox); ext1 i; rw [AlgHom.comp_apply,layBox, MvPolynomial.aeval_X,eyes, Labels.read,aeval_X];rfl
lemma layBox_hom (i:Labels.Key G) : IsWeightedHomogeneous (vapor G) (layBox (MvPolynomial.X i)) (Labels.generation i):= by
    rw [layBox,MvPolynomial.aeval_X]; have h:= gears (E:=Okay G) (i.1+1) ((realSign i) ∘ₗ (shelve (G:=G) i.1)); exact h

def fallIn(n:ℕ):poly (KeyIn G n)→ₐ[ℂ] Book G:= layBox.comp (MvPolynomial.rename (Subtype.val : KeyIn G n→ Labels.Key G))
lemma fall_apply (i: Labels.Label G n): fallIn n (thawKey i)=layBox i.val:=by rw [fallIn,AlgHom.comp_apply,returns]
lemma fall_hom (i:KeyIn G n) : IsWeightedHomogeneous (vapor G) (fallIn n (MvPolynomial.X i)) (Labels.generation i.val):=by rw [fallIn,AlgHom.comp_apply,rename_X]; exact layBox_hom _
lemma plus₁ (p:Film G n) : 0<bear p:= by cases p<;>simp [bear, Labels.generation]
def faceOp (k m:ℕ):poly (Film G k)→ₐ[ℂ] Book G:= (trumpet (Okay G) valP m).comp (assignP k)
lemma face_up (k m:ℕ): Raises bear (vapor G) (faceOp k m):= by
   intro i; let b:=bear i -1; have he: bear i=b+1:= by have := plus₁ i; unfold b; omega
   change Strong Φ (bear i) (trumpet _ _ m (assignP k (MvPolynomial.X i))); rw [he, assign_post,tru]; exact bulges (i:=postP k i) (m:=bear i - 1) (occ Heat.Ray.address k i) m -- occ metav
lemma full_head (k m:ℕ)(h:k≤m): Ready (LiftMark.key G k) (vapor G) ((faceOp k m).comp (rename Sum.inl)) (fallIn k):= by
   rintro ⟨⟨n,i⟩,hi⟩; let l: KeyIn G k:= ⟨⟨n,i⟩,hi⟩
   change level Φ (n+2) _= level Φ (n+2) (fallIn k (MvPolynomial.X l))
   rw [trimmer_hom (le_refl (n+2)) (show IsWeightedHomogeneous Φ (fallIn k (MvPolynomial.X l)) (n+2) from fall_hom l)]; rw [AlgHom.comp_apply,rename_X,faceOp,AlgHom.comp_apply,assign_post]
   let v:= postP k (.inl l); let j:Film G k:= .inl l
   have hv:v∈grads G (n+1):= by have h:=occ Heat.Ray.address k j; rwa [show bear j -1=n+1 by change n+1+1-1=n+1; omega] at h
   change level Φ (n+2) (trumpet (Okay G) valP m (glyph (com v)))=_; rw [lite hv m (lt_of_lt_of_le hi h)] -- nat lt?
   rw [fallIn,AlgHom.comp_apply,rename_X,layBox,aeval_X]; apply probe_ext; intro x; rw [pillar _ _ x (n+1) rfl,eyes, taste_eval, lif]
   apply congr_arg; let X:= x (n+1); let Z:= ((X).val.val)
   change flatL (port _ X.val) v= realSign l.val (shelve n X); rw [show flatL (port _ X.val) v= _ from owed Heat.Ray.address i (n:=n) (d:=k) hi X.val];rfl -- inspect
lemma bloom_word (X:Word G): bloom X.d (looking X)=layBox (labelledP X).val := by
    rw [← loom_eq X.d]; let n:= X.d; let p:= labelledP X; let F:=faceOp (G:=G) n n; let Z:= (thawKey p); have Hp:IsWeightedHomogeneous (LiftMark.key G n) Z n:= thaws (pureR X)
    have hu := face_up (G:=G) n n; change level Φ n (F (world n X))=_; rw [← hu.trim, restored X (le_refl X.d)];
    change level Φ n ((F.comp (rename Sum.inl)) Z)=_; have hh:=full_head (G:=G) n n le_rfl; rw [hh.feed ?_ ?_ (Strong.of_pure Hp), trimmer_hom le_rfl (hom_feed _ (fall_hom (G:=G)) Hp),fall_apply];
    · intro i; rw [AlgHom.comp_apply, rename_X];exact hu _
    · intro i; exact Strong.of_pure (fall_hom i)
end YM.PositionX.Grow
