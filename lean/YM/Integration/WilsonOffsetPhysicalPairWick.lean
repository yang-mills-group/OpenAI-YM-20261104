import YM.Integration.WilsonOffsetJointWick
import YM.Integration.WilsonOffsetPhysicalPair

/-! The real cutoff pair, with both transfer-terminal inverses and fine
engineering dimensions, tested against two independently posed, joint Wilson
Wick banks. The total coefficient invoice is shown, before any scaling claim. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetPhysicalPairWick
open Function Filter Finset Lattice Wilson RG Source Labels Precision Tree Pressure
open PhysicalNext.Repeat.Legato MSbar MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Midpoint MSbar.Rolling Push.Uniform
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels WilsonOffsetConditionalCharge WilsonOffsetMarkComparison WilsonOffsetJointRoster
open WilsonOffsetPhysicalPair WilsonOffsetJointWick
open scoped Classical BigOperators
variable {G:Gauge} {a b:ℕ}

abbrev Index (G:Gauge) (a b:ℕ):=(((frames G).level a).Index × ((frames G).level b).Index)
def slot (t:Index G a b):Fin (two t.1 t.2).length:=⟨1,by change 1<2;decide⟩
def sufficient {f:Side} (t:Index G a b) (x z e center:Site f) (L:ℕ) (y:ℝ):Prop:=
  fits (two t.1 t.2) univ (seats t.1 t.2 x e) (slot t) z center L y
def target (R:Run G) (t:Index G a b) (k:ℕ) (A:MSbar.Mosaic.Issue G) (Z:Positions (Primary A.c G))
    (x z e:Site A.f):ℂ:=
  let o:=seats t.1 t.2 x e
  let w:=price R (two t.1 t.2) univ k A Z o (slot t)
  paint (w z)-paint (w e)
def coefficient (R:Run G) (N p:ℕ) (v:R.family.label a) (w:R.family.label b) (t:Index G a b):ℂ:=
  atom R N p v t.1*atom R N p w t.2

private theorem placed {f:Side} (t:Index G a b) (x z e:Site f):
    Function.update (seats t.1 t.2 x e) (slot t) z = seats t.1 t.2 x z:=by
  funext h;change Fin 2 at h
  fin_cases h <;> rfl

private theorem delta {f:Side} (t:Index G a b) (x z e:Site f) (U:Config G f):
    field (two t.1 t.2) (univ.erase (slot t)) (seats t.1 t.2 x e) U *
      (WilsonOffsetJointRoster.one (two t.1 t.2) (slot t) z U-WilsonOffsetJointRoster.one (two t.1 t.2) (slot t) e U)=
      planted t.1 t.2 x z U-planted t.1 t.2 x e U:=by
  have h:=paired (two t.1 t.2) univ (slot t) (mem_univ _) (seats t.1 t.2 x e) z e U
  rw [placed t x z e,placed t x e e] at h
  exact h.symm

theorem purchased (R:Run G) (u:G.ColorIndex) (rows:∀t:Roster G,FluctuationMaskReadings (lamps t) R u)
    (a b k L:ℕ) (D:ℝ) (hD:0≤D):
    ∀ᶠ m:ℕ in atTop,∀ n,
      (∃ S:Scene R.family.path.levels n (k+2),Realized R.alloy.B.kin (m+1) n m (k+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (k+2)) (ready:Realized R.alloy.B.kin (m+1) n m (k+2) (Lis.sun G u) S),
        let F:=(ready.step m (Nat.lt_succ_self m) le_rfl).choose;let dir:=(ready.step m (Nat.lt_succ_self m) le_rfl).choose_spec.choose
        let A:=sceneIssue (N:=m+1) (RunFormalChain.fromRun R) S F dir;let y:=R.family.path.levels.clock.hatBeta (m+1)
        ∀ Z:Positions (Primary A.c G),‖A.fClock • Z‖≤D*Heath.Cottage.room y →
        ∀ (v:R.family.label a) (w:R.family.label b) (x z e bz be:Site A.f),
        (∀t:Index G a b,sufficient t x z e bz L y ∧ sufficient t x e e be L y) →
        let V:=postcard G A.c A.fClock Z
        let c:=coefficient R (m+1) n v w
        ‖conditional A.S A.pre V (fun U=>R.family.O (m+1) n v x U*(R.family.O (m+1) n w z U-R.family.O (m+1) n w e U))-
          ∑t,c t*target R t k A Z x z e‖≤(∑t,‖c t‖)*(4*A.fClock^k):=by
  have all:=Filter.eventually_all.mpr fun t:Index G a b=>WilsonOffsetJointWick.purchased R u rows (two t.1 t.2) k L D hD
  filter_upwards [all] with m bought n
  have hm:=Nat.lt_succ_self m
  refine ⟨(bought (0,0) (m+1) n hm).1,?_⟩
  intro S ready
  dsimp only
  intro Z hZ v w x z e bz be cover
  let A:=sceneIssue (N:=m+1) (RunFormalChain.fromRun R) S (ready.step m hm le_rfl).choose (ready.step m hm le_rfl).choose_spec.choose
  let V:=postcard G A.c A.fClock Z
  let c:=coefficient R (m+1) n v w
  let diff (t:Index G a b) (U:Config G A.f):=planted t.1 t.2 x z U-planted t.1 t.2 x e U
  have source:(fun U=>R.family.O (m+1) n v x U*(R.family.O (m+1) n w z U-R.family.O (m+1) n w e U))=(fun U=>∑t,c t*diff t U):=by
    funext U;rw [Fintype.sum_prod_type]
    exact relative R v w x z e U
  have per (t:Index G a b):‖conditional A.S A.pre V (diff t)-target R t k A Z x z e‖≤4*A.fClock^k:=by
    have h:=(bought t (m+1) n hm).2 S ready Z hZ univ (slot t) (mem_univ _) (seats t.1 t.2 x e) z e bz be (cover t).1 (cover t).2
    simpa only [delta,target,diff,A,V] using h
  have hk:A.S.IsKernel A.pre.beta G:=R.family.path.levels.transition_mass m n A.pre.beta
  have hp:RG.Envelope A.pre.eval:=A.pre.envelope (R.makes.wilson.represents (m+1) n (m+1) le_rfl).good
  have cont (t:Index G a b) (y:Site A.f):Continuous (planted t.1 t.2 x y):=
    tally_cont (packet ⟨two t.1 t.2,univ⟩) (fun j=>seats t.1 t.2 x y j.val)
  have smooth (t:Index G a b):Continuous (diff t):=(cont t z).sub (cont t e)
  change ‖conditional A.S A.pre V (fun U=>R.family.O (m+1) n v x U*(R.family.O (m+1) n w z U-R.family.O (m+1) n w e U))-
    ∑t,c t*target R t k A Z x z e‖≤(∑t,‖c t‖)*(4*A.fClock^k)
  have iden:conditional A.S A.pre V (fun U=>R.family.O (m+1) n v x U*(R.family.O (m+1) n w z U-R.family.O (m+1) n w e U))=
      ∑t,c t*conditional A.S A.pre V (diff t):=(congrArg (conditional A.S A.pre V) source).trans
        (WilsonOffsetSourceBasis.combination hk hp V c diff smooth)
  apply (congrArg (fun q:ℂ=>‖q-∑t,c t*target R t k A Z x z e‖) iden).le.trans
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (per t) (norm_nonneg _)

end YM.Integration.WilsonOffsetPhysicalPairWick
