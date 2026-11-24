import YM.RegulatorIR.Profiles.Consumer

/-!
# All-level-cover translations, needed for center readout
Coordinate-choice branch. Some frame invariance (through polynomial operations)
independent of sizes of supplied moments. Layer bill cost hypotheses separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I X Y A B Z:Type}{q u b p a i e k d m:ℕ}{M: W→ℕ}{n:Page M→Side}
section Scalars
variable {P:ℝ}{K:Layer X X}(D:Equiv.Perm X)(V:Equiv.Perm Y)
variable (h:Echos.Level D K) {R: Orders X} (H:∀ i j,Echos D (R i j) (R i j))
include h H
lemma smoke (s:Bool):(∀ k i j,Echos D (logHeat K R s k i j) (logHeat K R s k i j)):=by
 intro k; induction k using Nat.strong_induction_on with
 | _ k ih=>
    intro i j;cases k
    · rw [logHeat_first];split; exact fun _=>rfl; exact H i j
    next k=>
      rw [logHeat_next];split;exact fun _=>rfl
      apply Echos.times; apply Echos.add
      · exact Echos.times (Echos.sync (Echos.ferries h (ih k (by omega) i (j+2)))) _
      apply Echos.times; unfold drift; apply Echos.sums; intro x hx; unfold Diagram.carry; apply Echos.sums;intro y hy; unfold force; apply Echos.sums;intro v hv; have hu:= Finset.mem_antidiagonal.mp hx; rw [← Finset.mem_antidiagonal.mp hv]; exact Echos.taps h (ih _ (by omega) _ _) (ih _ (by omega) _ _)
variable {C:Deck P X A}{F:Deck P Y B}{S:GridStep C F}
omit h H in
lemma aroma (ha:Echos D (R i p) (R i p))(hx:Echos (Equiv.sumCongr D V) (S.addon i p) (S.addon i p)): Echos (Equiv.sumCongr D V) (S.jVac R i p) (S.jVac R i p):=by
 have he:= excess D V (R i p); rw [← ha.only] at he
 exact Echos.add he hx
variable (hv:Echos.Level (Equiv.sumCongr D V) S.line)(ha:Echos.Level (Equiv.sumCongr D V) S.driftL) (hB:∀ i j,Echos (Equiv.sumCongr D V) (S.addon i j) (S.addon i j)) {T U:Orders X}
omit h
include hv ha hB
lemma smolder (i k): Echos V (S.pure R i k) (S.pure R i k):=by
 unfold GridStep.pure;split;exact fun _=>rfl
 have hx := smoke (Equiv.sumCongr D V) hv (fun i j=> aroma D V (H i j) (hB i j))
 intro x; apply Echos.fresh ha _ (acrossT (lastChannel C F).native x)
 unfold ceaseHeat heated; apply Echos.sums; exact fun _ _=>hx false _ _ _
lemma flames (hh :∀ i j,Echos D (T i j) (U i j))(i k) : Echos V (S.each m R T i k) (S.each m R U i k):=by
 intro x; apply Echos.fresh ha _ (acrossT (lastChannel C F).native x); apply Echos.heat hv
 · exact smoke (Equiv.sumCongr D V) hv (fun i j=>aroma D V (H i j) (hB i j)) false
 intro i j; have he:=excess D V (T i j); rw [← (hh i j).only] at he;exact he
end Scalars

lemma jetMoves (V:Equiv.Perm I)(F:Equiv.Perm X)(T:X→Micro I)(Q:X→Orders I) (f:X→ℝ)(k:X→ℕ)
    (hp:∀ i,Lab (k i) (f i) (T i) (Q i))(he:∀ i t v,T (F i) t v=T i t (v∘V))(hf:∀ i,f (F i)=f i)(hh:∀ i,k (F i)=k i):∀ i j, Echos V (many Q i j) (many Q i j):=by
 have hz(i e):(Q (F i)) e=fun r=>echo V (Q i e r):=by
    have ha:= hp (F i);rw [hf,hh] at ha;have hb:=hp i
    cases Nat.eq_zero_or_pos e with
    | inl hy=> subst e; rw [ha.awake,hb.awake];rfl
    | inr ht=>
      refine guessed (ha.scope_ e) ?_ ?_ ?_ ?_
      · intro r h; exact hb.scope_ e r (fun h' => h (by dsimp only;rw [h',echo_zero]))
      · exact ha.smooth e
      · intro r; exact echo_sym (hb.smooth e r)
      intro x; rw [ha.figures x ht,show flank (T (F i)) x=flank (T i) (x∘ V) from funext fun t=>he i t (t • x), ← hb.figures (x ∘ V) ht]; apply Finset.sum_congr rfl; intro j _; dsimp only
      rw [strum_perm x V]; rw [show (fun z: Tuple I j=> echo V (Q i e j) (V ∘ z))=Q i e j from funext (echos _ _)]
 intro i j x; unfold many massive; rw [← F.tsum_eq]; apply tsum_congr; intro y; dsimp only; rw [hz];exact echos ..

private lemma stride (T: Cover) (R:Scale)(x : Face ℤ)(t:ℝ)(v:Foot G→ℝ) : plain R G (plateTrans T x) t v=plain R G x t (v ∘ carryX T):=by
 unfold plain; rw [← carrier]; have h:= Face.send_price (win G v) x 1 T G.price G.price_inv fun x g=> G.price_conj ..; rw [summer_dir,pull_one] at h; rw [h]
section Geometry
variable {c f:Side}(S:StepData c f)
-- adjust any period, even predicate needed in fiber proper
def strideR (x:Cover) := S.patch.L.val • x
private def walkP (a:Site c) (u:Edge (Site f)): Edge (Site f):= (u.1+S.ratio.embed a,u.2)
lemma trunk_moves (a: Site c)(u: Edge (Site f)): u∈(bios S).trunks → walkP S a u∈ (bios S).trunks:=by
 rw [Forest.trunk_mem_iff, Forest.trunk_mem_iff]; rintro ⟨x,hx,rfl⟩
 refine ⟨x+S.ratio.embed a, (Fibers.shifted_leaf ..).mpr hx,?_⟩
 unfold bios; rw [repeat_patch]; unfold Lattice.Step.used walkP; split_ifs <;> first| rfl| (dsimp only; congr 1; abel)
lemma branch_path (a:Cover)(x:Edge Cover): branch (bios S) (resolve f (dis (strideR S a) x))=branch (bios S) (resolve f x):=by
 apply propext
 let v:=wrap c a;let w:=around f x
 unfold resolve; rw [bone (F:=bios S) (Field.Square.proper ..),bone (F:=bios S) (Field.Square.proper ..)]
 have hp:around f (dis (strideR S a) x)=walkP S v w:= Prod.ext (by change wrap _ (_+_)= _+_;rw [add_comm,map_add];rw [show S.ratio.embed v= _ from Ratio.embed_wrap ..];rfl) rfl
 rw [hp]; refine ⟨fun hx=> ?_, trunk_moves S v w⟩
 have hv:= trunk_moves S (-v) _ hx;rw [show walkP S (-v) _=w from Prod.ext (by unfold walkP; dsimp only;rw [show S.ratio.embed (-v)= -S.ratio.embed v from S.ratio.root.map_neg _]; abel) rfl] at hv; exact hv
abbrev bundleS (p:Cover): Equiv.Perm (Foot G⊕ Foot G):= Equiv.sumCongr (carryX (strideR S p)) (carryX p)
private def tour (p:Cover): Equiv.Perm (Edge Cover):= Equiv.prodCongr (Equiv.addLeft p) (Equiv.refl _)
private def gridS (p:Cover): Equiv.Perm Branchix:= Equiv.sumCongr (tour (strideR S p)) (tour p)
lemma flavour_v (p:Cover)(R:Scale){W:Branchix→Orders (KFoot G)}(h:Sphere S (bios S) R W):∀ i j,Echos (bundleS S p) (many W i j) (many W i j):=by
 refine jetMoves _ (gridS S p) _ _ _ _ h ?_ (fun x=>by cases x<;> rfl) (fun x=>by cases x<;> rfl)
 rintro (x|x) t v
 · change carnal S (bios S) (dis (strideR S p) x) t v=carnal S (bios S) x t (v ∘ bundleS S p); rw [carnal,carnal,branch_path]; rfl
 change opi S _ (dis p x) t v=opi S _ x t _; unfold opi
 change _* G.price (win G (v ∘ Sum.inr) _ * _) =_* G.price (win G ((v ∘ Sum.inr) ∘ carryX p) _ * (pond _ _ (win G ((v ∘ Sum.inl) ∘ carryX _)) _)⁻¹)
 rw [← carrier,← carrier, strideR,pulled (S:=S)]; simp only [dis, translate]; rw [add_comm x.1]
end Geometry
section Supply
variable {W : Type}{S:Heir n G}{R: Reel S}{T:S.Accounts}(h:Common R)(hv:R.Follows T)
-- use translation invariance of K and Dtr (owned RG08) under all coarse periods. Assert in literal orientation and tree branch. Can attempt reduce under moment hypotheses later.
structure Passage (R:Reel S) : Prop where
 honor : ∀ i:Flap M,∀ t x y,R.Dtr i (carryX (strideR (R.steps i) t) x) (carryX t y)=R.Dtr i x y
 suited : ∀ i:Flap M,∀ t, Echos.Level (carryX (strideR (R.steps i) t)) (R.pulses i)
namespace Passage
variable (H: Passage R)
include H
lemma levels (w:Flap M)(p:Cover): Echos.Level (bundleS (R.steps w) p) (S.frames w).line ∧ Echos.Level (bundleS (R.steps w) p) (S.frames w).driftL:=by
 rw [R.bondF,R.meanF]; refine ⟨?_,?_⟩
 · rintro (i|i) (j|j)<;> first|exact H.suited w p i j| rfl
 rintro (i|i) (j|j) <;> first| exact H.honor w p j i|rfl | (change ID (Foot G) (carryX p j) (carryX p i) = ID _ j i; simp only [ID,Equiv.apply_eq_iff_eq]; congr)
include h
omit H in
lemma assets (w:Flap M)(p:Cover)(i j): Echos (bundleS (R.steps w) p) ((S.frames w).addon i j) ((S.frames w).addon i j):=by
 obtain ⟨v,hv,hp⟩:=R.powers w; rw [hp]; rw [h w] at hv;exact flavour_v (R.steps w) p (R.clock w.prev) hv i j
include h hv in
lemma cells : ∀ (i: Page M)t e j,Echos (carryX t) (T.bulk i e j) (T.bulk i e j):=by
 refine Page.proves (fun w t e j=> ?_) ?_
 · obtain ⟨p,h,hv,H⟩:= hv w; rw [hv]; exact jetMoves (carryX t) (Equiv.prodCongr (Equiv.addLeft t) (Equiv.refl _)) (fun i=>plain _ G i) p _ _ h (stride t _ ) (fun _=>rfl) (fun _=>rfl) e j
 intro w hx t e j; rw [← T.step_v]; exact smolder (carryX (strideR (R.steps w) t)) (carryX t) (hx _) (H.levels w t).1 (H.levels w t).2 (assets h w t) e j
end Passage
end Supply
end YM.RegulatorIR.Profiles
