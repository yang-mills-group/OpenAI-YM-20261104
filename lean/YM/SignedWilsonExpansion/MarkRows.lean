import YM.SignedWilsonExpansion.BulkTop
namespace YM.SignedWilsonExpansion.MarkRows
/-! The actual rank-two letters, with the continuation fixed by the independent Victor. Linear combinations are fixed before any scale evaluation. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Garment MS.Heat MS.Rock.Path MS.Rake
open MS.Heat.Base
open BulkTop HighRank HighScale TreeLine TreeView
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{B:Deck G}{M:Booked B} (S:MS_Data G M)
abbrev I (B:Deck G) := B.BIndex 4 2
abbrev address (i:I B): Plaid B 4:= ⟨⟨2,by decide⟩,i⟩
variable (x:I B→ℝ)
def ground : Law G:= ∑ i:I B,(x i:ℂ) • (Land.read (address i)).read
def packet : Recount G:= ∑ i:I B,(x i:ℂ) • Archive 4 (S.marks 4 (address i))
local notation "R" => packet S x
local notation "N" => ground x
local notation "U" => Archive 4 S.bulk
variable {A:Flats G}{d:ℕ}{D:Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP}
lemma own (n:ℕ)(s:Clock ℝ): R n s= ∑ i:I B,(x i:ℂ) • ear S (address i) n s:=by unfold packet; simp only [Finset.sum_apply,Pi.smul_apply,ear]
lemma cycle_pass (K:Arts.Rip G)(s:Clock ℝ)(cost:rPrice K)(ok:Host A d): Pass (K 0) (four d A s) (covMeasure Axis):= by
  intro l
  have hv:Integrable (fun p=>trc (K 0) p (four d A s) l) volume:= Rock.Path.theory («U»:=K) (F:= hereZ d A s.2 s.1) (blade0 ok|>.price) cost 0 l
  exact hv.smul_measure (by finiteness)
lemma marked_pass (s:Clock ℝ)(t:ℝ)(i:I B)(n:ℕ): Pass (PlanetD G t) (ear S (address i) n s) (covMeasure Axis):=
  cycle_pass (Garment.Wick.A0 G t) s (Garment.Wick.A_caps G t|>.price) (Host.host (Dock.gang (S.markOK 4 (address i) n)))
lemma mark_clock (n:ℕ)(s:Clock ℝ)(t:ℝ) : Pass (PlanetD G t) (R n s) (covMeasure Axis) := by
  rw [own]; exact cc_sum1 _ _ fun i _=>cc_scale _ (x i:ℂ) (marked_pass S s t i n)

lemma loop_apply (n:ℕ)(t:Clock ℝ)(D:Needle G)(live:∀i:I B,Pass (D.meter t.2) (ear S (address i) n t) D.measure):
    cycle (D.meter t.2) D.measure (R n t)=∑ i:I B,(x i:ℂ) • cycle (D.meter t.2) D.measure (ear S (address i) n t):= by
  rw [own]; change Ccy _ _ _=_
  rw [cc_sum _ _ (fun i _=>cc_scale _ _ (live i))]; exact Finset.sum_congr rfl fun i _=> ccy_s _ _

lemma tree_apply (D:Needle G)(n:ℕ)(t:Clock ℝ) : D.using_tree n 0 1 (fun j=>U j t) (fun j=>R j t) t.2=
    ∑ i:I B,(x i:ℂ) • D.using_tree n 0 1 (fun j=>U j t) (fun j=>ear S (address i) j t) t.2:= by
  unfold using_tree; simp_rw [one_smul, ←blvd, own,map_sum,map_smul,Finset.smul_sum]; rw [Finset.sum_comm]

lemma program (n:ℕ)(D:Needle G)(t:Clock ℝ)(h:∀i:I B,Pass (D.meter t.2) (ear S (address i) n t) D.measure):
    recu D 0 1 U R n t=∑ i:I B,(x i:ℂ) • recu D 0 1 U (ear S (address i)) n t:= by
  unfold recu; rw [tree_apply,loop_apply S x n t D h]; simp_rw [smul_add, Finset.sum_add_distrib]

lemma sheared (n r :ℕ) : Covariant (R n) false r 4:= by
    intro y t s w hc hx; rw [own,own]; unfold Port.shift; simp only [Finset.sum_apply,Pi.smul_apply, Finset.mul_sum];
    apply sum_congr rfl; intro i _; have H: ear S (address i) n (y,t)=Port.shift 4 s (ear S (address i) n (y+s,t-s)):= Port.Bx4 (markView S (address i) n|>.host); rw [H]; change _= _*((x i:ℂ)*_); unfold Port.shift; rw [smul_eq_mul,mul_left_comm]
lemma renew (n:ℕ): stamp (R n) := by
    have h: (fun y t=> R n (y,t))= ∑ i:I B,(x i) • fun y t:ℝ=>ear S (address i) n (y,t):= by
      ext1 y; ext1 t; rw [own]; simp_rw [Finset.sum_apply]; rfl
    rw [High.stamp,h]; exact Logarithm.Ready.sums _ fun i _=> Logarithm.Ready.scale (plant (markView S (address i) n|>.host)) _
lemma polish (n:ℕ)(t:Clock ℝ): Polish (R n t):= by
    intro E _ _ w; unfold fieldVal; simp_rw [own,Finset.sum_apply]; exact ContDiff.sum fun i _=> (Outlook.hair (markView S (address i) n|>.host) (n:=0) w).const_smul (x i:ℂ)
lemma solid (n:ℕ)(t:Clock ℝ): Solid false (R n t) 0:=by
  rw [own]; let T (w: Finset (I B)) : Law G:= ∑ i∈w, (x i:ℂ) • ear S (address i) n t
  suffices ∀w,Solid false (T w) 0 from this _
  intro w; induction w using Finset.induction_on with
  | empty=> convert solid_zero; simp [T]
  | insert i w hi ih=> unfold T; rw [Finset.sum_insert hi]; exact Solid.add (((mark_sphere S (address i)).master.trueC n t).scalar _) ih
lemma starts (t:Clock ℝ)(w:Legs (Lane4 G))(hw:1≤w.length): R 0 t w=N w:= by
  rw [own]; simp_rw [ground,Finset.sum_apply, Pi.smul_apply, mark_zero S (address _) t w (show _=2 from rfl) hw]
lemma level1 (t:Clock ℝ) : Upper false 3 (R 1 t):= by
  intro w he h; rw [own, Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=>by rw [Pi.smul_apply,mark_one_height S (address i) t rfl _ he h,smul_zero]
lemma level2 (t:Clock ℝ) : Upper false 4 (R 2 t):= by
  intro w he h; rw [own, Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=>by rw [Pi.smul_apply,mark_two_height S (address i) t rfl _ he h,smul_zero]
variable {b:Bool}{D H Q P : Reading G}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {w : Wire (Branch G Axis) E FourP}
lemma track_add (h:Track b D H w)(hr:Track b Q P w): Track b (D+Q) (H+P) w:= by
  intro hw; obtain ⟨ht,hA,hT⟩:=h hw; obtain ⟨hf,hB,hF⟩:=hr hw
  refine ⟨fun i=>(ht i).add (hf i),fun i=>(hA i).add (hB i),fun i t x j=>?_⟩; obtain he:= (hT i t x j).add (hF i t x j); convert! he using 1
  · funext t'; change iteratedFDeriv ℝ j (Chart D w (i,t')+Chart Q w (i,t')) x=_; rw [iteratedFDeriv_add ((ht _).of_le (by exact_mod_cast le_top)) ((hf _).of_le (by exact_mod_cast le_top)) ]; rfl
  change iteratedFDeriv ℝ j (Chart H w (i,t)+Chart P w (i,t)) x=_; rw [iteratedFDeriv_add ((hA _).of_le (by exact_mod_cast le_top)) ((hB _).of_le (by exact_mod_cast le_top)) ]; rfl
lemma track_smul (h:Track b D H w)(v:ℂ): Track b (v • D) (v • H) w:= by
  intro hw; obtain ⟨ht,hA,hT⟩:=h hw
  refine ⟨fun i=>(ht i).const_smul v,fun i=>(hA i).const_smul v,fun i t x j=>?_⟩; obtain he:= (hT i t x j).const_smul v; convert! he using 1
  · funext t'; change iteratedFDeriv ℝ j (v • Chart D w (i,t')) x=_; exact iteratedFDeriv_const_smul_apply ((ht _).contDiffAt.of_le (by exact_mod_cast le_top))
  change iteratedFDeriv ℝ j (v • Chart H w (i,t)) x=_; exact iteratedFDeriv_const_smul_apply ((hA _).contDiffAt.of_le (by exact_mod_cast le_top))
lemma track_sum {ι:Type}(K:Finset ι){f g:ι→ Reading G}(h:∀ i ∈ K, Track b (f i) (g i) w) : Track b (∑ i∈K,f i) (∑ i∈K,g i) w:= by
  induction K using Finset.induction_on with
  | empty=> rw [Finset.sum_empty,Finset.sum_empty]; intro _; refine ⟨fun _=>contDiff_const,fun _=>contDiff_const, fun i t x n=>?_⟩; change HasDerivAt (fun b:ℝ=>iteratedFDeriv ℝ n 0 x) (iteratedFDeriv ℝ n (0:E→ℂ) x) t; simp_rw [iteratedFDeriv_zero]; exact hasDerivAt_const ..
  | insert t K ht ih=>rw [sum_insert ht,sum_insert ht]; exact track_add (h t (by simp)) (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma speed (e:ℕ)(w:Wire (Branch G Axis) E FourP): Track false (R e) (recu (spaceD G) 0 1 U R e) w:= by
  have ht: recu (spaceD G) 0 1 U R e= ∑ i:I B,(x i:ℂ) • recu (spaceD G) 0 1 U (ear S (address i)) e:= by
    funext t; simp only [ Finset.sum_apply,Pi.smul_apply,program S x e _ t (fun i=>marked_pass S t t.2 i e)]
  rw [ht,packet, Finset.sum_apply]; exact track_sum _ (fun i _=> track_smul ((mark_sphere S (address i)).master.road E w e (by omega) (fun h=>Bool.noConfusion h)) _ )
lemma identities (e:ℕ)(t:Clock ℝ)(w:Legs (Lane4 G)): natQ (R e t) w=Ward id (spaceD G) e 0 1 U R t w:= by
  rw [own,map_sum]; unfold Ward
  have he i:Pass ((degreeMaster id (spaceD G)).meter t.2) (ear S (address i) e t) ((degreeMaster id (spaceD G)).measure):= cycle_pass (Garment.Wick.B0 G t.2) t (Garment.Wick.B_caps G t.2|>.price) (markView S (address i) e|>.host)
  simp_rw [program S x e _ t he, ← Finset.sum_neg_distrib, Finset.sum_apply,map_smul, Pi.smul_apply]; refine Finset.sum_congr rfl fun i _=>?_; rw [show natQ _ _=_ from (mark_sphere S (address i)).master.qfm e t _ (Nat.zero_le _) (fun h=>Bool.noConfusion h) (fun h=>Bool.noConfusion h)]; exact smul_neg ..
lemma licensed : N ∈ B.carries 4 2:= by
  unfold ground; refine Submodule.sum_mem _ fun i _=>?_
  exact B.carries 4 2 |>.smul_mem (x i) (B.form 4 2 i)
lemma born : Solid false N 0 ∧ Form N wfield 4 false ∧ Ranked false 2 N := lease_one.mp (lease_enough G (B.le (licensed x)))
lemma ground_symm: Symm (field parity) N := fun l i j k=> (born x).1.symm l i j k (fun h=>Bool.noConfusion h)
lemma upper0 (t:Clock ℝ): Upper false 2 (R 0 t):= fun w hc hw=> (starts S x t w (by omega)).trans ((born x).2.2 w hc (by omega))
end
end YM.SignedWilsonExpansion.MarkRows
