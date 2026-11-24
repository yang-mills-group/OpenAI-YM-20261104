import YM.RegulatorIR.Profiles.Graft

/-!
# Algebra for finite root broadcasts

Only uses linearity through *assessed p* because bulk inputs might not be
summable past that. Coefficient-wise. Normalized by denominator throughout
on cover. (Contour exponent and label reexpression elsewhere.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Sources
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
-- homogeneity without any finiteness premises; sum exchange later
section Costs
variable (c₀:ℝ)
lemma scaleSym (W:Packet X p) : Packet.symmetry (c₀ • W)=c₀ • Packet.symmetry W:=by
 ext x;rw [Pi.smul_apply,smul_eq_mul,symmetry_at,symmetry_at,mul_left_comm,Finset.mul_sum _ _ c₀]; rfl
lemma scaleO (F:X↪Y)(W: Packet X p): offer F (c₀ • W)= c₀ • offer F W:=by ext1 x;rw [offer,Pi.smul_apply,offer];unfold Stalk.collect; exact tsum_mul_left
lemma scaleK (K:Layer X X)(W:Packet X (p+1))(V:Packet X (a+1)) : knot K (c₀ • W) V=c₀ • knot K W V:=by
 ext x;rw [knot,knot,splice,Pi.smul_apply,splice, smul_eq_mul, ← tsum_mul_left];apply tsum_congr;intro z;exact mul_assoc ..
lemma scaleP (K:Layer X X)(W: Packet X (r+2)): Packet.loop (c₀ • W) K=c₀ • Packet.loop W K:=by
 ext x; rw [loop,Pi.smul_apply, loop, smul_eq_mul,← tsum_mul_left];apply tsum_congr; intro z;unfold curve;change _*(c₀ * _)= _;ring
lemma scaleDraft (K:Layer X X)(W: Packet X r): draft K (c₀ • W)=c₀ • draft K W :=by
 unfold draft; generalize List.finRange r=l
 rw [← scaleSym];apply congr_arg; induction l with
 | nil=> rfl
 | cons a l ih=>
    rw [Budget.Packet.drawing,Budget.Packet.drawing,ih]; ext1 x; rw [Packet.ray,Pi.smul_apply, Packet.ray,smul_eq_mul,← tsum_mul_left];apply tsum_congr;intro z;unfold Packet.swivel;change _*(c₀ * _) = _;ring
lemma scaleHeat (K:Layer X X)(V:ℕ→Orders X)(T:Orders X): markHeat K V (c₀ • T) k e r= c₀ • markHeat K V T k e r:=by
 induction k using Nat.strong_induction_on generalizing e r with
 | _ k ih=>
    cases k with
    | zero=>rw [markHeat_first,markHeat_first]; rfl
    | succ k=>
      rw [markHeat_next,markHeat_next, smul_comm c₀ ];apply congr_arg;rw [smul_add c₀];apply congr_arg₂ (·+·)
      · rw [heating,heating,ih k (by omega),scaleP,scaleSym,smul_comm c₀]
      unfold drift; rw [Finset.smul_sum]; apply sum_congr rfl;intro t ht; unfold Diagram.carry; rw [Finset.smul_sum]; apply sum_congr rfl;intro i hi; unfold force; rw [Finset.smul_sum]; apply sum_congr rfl;intro j hj; rw [← Finset.mem_antidiagonal.mp hj,matchTwo,matchTwo,dif_pos rfl,dif_pos rfl, ih t.1 (by have :=mem_antidiagonal.mp ht;omega), scaleK c₀,scaleSym, smul_comm c₀]
variable {P:ℝ}{E:Deck P X A}{F: Deck P Y B}
lemma homogenous (J:GridStep E F)(T R:Orders X): J.each m T (c₀ • R)=c₀ • J.each m T R:=by
 let c:= (firstChannel E F).native;let Z:= fun i j=> offer c (R i j); let Q:=logHeat J.line (J.jVac T) false; let f:=endHeat m J.line Q Z; let L:= J.driftL
 have hz : (fun (e r:ℕ)=> offer c ((c₀ • R) e r))=c₀ • Z:=funext fun _=> funext fun _=>scaleO c₀ c _
 have ht : endHeat m J.line Q (c₀ • Z)= c₀ • f:=by
    ext1 e;ext1 i; unfold f endHeat heated; rw [Pi.smul_apply,Pi.smul_apply]; rw [Finset.smul_sum]; exact sum_congr rfl fun _ _=>scaleHeat ..
 ext1 e;ext1 r; unfold GridStep.each;rw [hz,ht,Pi.smul_apply,Pi.smul_apply]; change crop _ (draft L (c₀ • _))=_;rw [scaleDraft]; rfl
lemma const_v (J:GridStep E F)(T:Orders X): J.each m T 0=0:=by simpa using homogenous (m:=m) 0 J T 0

-- equality restriction. no rank assumptions
variable {T V: Orders X}{Q: ℕ→ Orders X}
lemma survivesH (K: Layer X X) (h : ∀ i,i≤p→T i=V i)(he:e ≤ p) (k): markHeat K Q T k e r=markHeat K Q V k e r:=by
 induction k using Nat.strong_induction_on generalizing e r with
 | _ k ih=>
    cases k
    · rw [markHeat_first,markHeat_first,h e he]
    next k=>
      rw [markHeat_next,markHeat_next,heating,heating,ih k (by omega) he];apply congr_arg;apply congr_arg
      unfold drift;apply sum_congr rfl;intro i hi; unfold Diagram.carry;apply sum_congr rfl;intro j hj; unfold force; apply sum_congr rfl; intro s hs; rw [← mem_antidiagonal.mp hs, matchTwo, matchTwo,dif_pos rfl,dif_pos rfl];rw [ih i.1 (by have he':=mem_antidiagonal.mp hi;omega) (by have he':=mem_antidiagonal.mp hj;omega)]
lemma survivesP (J:GridStep E F)(R:Orders X)(h:∀ i,i ≤ p→ T i=V i)(he:e ≤ p): J.each m R T e=J.each m R V e:=by
 ext1 r; unfold GridStep.each; apply congr_arg; unfold endHeat heated; apply Finset.sum_congr rfl; intro k _; exact survivesH _ (fun i hi=> by rw [h i hi]) he _
end Costs

section Transmission
variable {S:Heir n G}{T:S.Accounts}
variable (H:Milieu S T k p L)(w:Flap M)
local notation "P" => S.frames w
variable {A B:Orders (Foot G)}
include H
omit H in
lemma plusPrice {X:Type}{A B:Orders X}(hx:Cluster.Bill A p)(hz:Cluster.Bill B p): Cluster.Bill (A+B) p:= fun i hi r=> ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hx i hi r,hz i hi r⟩) (quota_add ..)
omit H in
lemma sigmaPrice {X:Type}{A:J→Orders X}(t: Finset J)(h:∀ i∈t,Cluster.Bill (A i) p): Cluster.Bill (∑ i∈t,A i) p:=by
 induction t using Finset.induction_on with
 | empty=>rw [sum_empty]; exact fun _ _ i=>by rw [show (0:Orders X) _ i=0 from rfl, quota_zero];finiteness
 | insert a s ha ih=> rw [sum_insert ha]; exact plusPrice (h a (mem_insert_self ..)) (ih (fun a hx=> h a (mem_insert_of_mem hx)))
omit H in
lemma scalePrice {X:Type}{A:Orders X}(h:Cluster.Bill A p)(s:ℝ): Cluster.Bill (s • A) p:=fun i hi r=>by change quota (fun x=>s*A i r x) _≠_;rw [quota_times];exact ENNReal.mul_ne_top (by finiteness) (h i hi r)
lemma Plus (hx: Cluster.Bill A p)(hh:Cluster.Bill B p) (he:e ≤ p): ((P).each m (T.bulk w.prev) (A+B)) e=(P).each m (T.bulk w.prev) A e+(P).each m (T.bulk w.prev) B e:=by
 let i:= (P).each m (T.bulk w.prev); change i (A+B) _=_; let C:=A+B
 have hw:= each_minus (A:=fun _=>C) (B:=fun _=>B) S.lifts (Cluster.Vac S T) (H.fund (b:=k) le_rfl) (H.solid le_rfl) (n:=m) w (plusPrice hx hh) hh he
 change i (C-B) e=i C e-i B e at hw; unfold C at hw;rw [add_sub_cancel_right] at hw;rw [show (P).each m (T.bulk w.prev) A e=_ from hw]; abel
lemma dividends (s: Finset J)(W:J→Orders (Foot G))(h:∀ i∈s, Cluster.Bill (W i) p)(he:e≤p): (P).each m (T.bulk w.prev) (∑ i∈s,W i) e=∑ i∈s, (P).each m (T.bulk w.prev) (W i) e:=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty,const_v];rfl
 | insert a s ha ih=> rw [sum_insert ha,sum_insert ha,Plus H w (h a (mem_insert_self ..)) (sigmaPrice _ (fun b hb=>h b (mem_insert_of_mem hb))) he, ih (fun i hi=>h i (mem_insert_of_mem hi))]
lemma estimateM (h:Cluster.Bill A p): Cluster.Bill ((P).each m (T.bulk w.prev) A) p:=by
 let f:= (firstChannel (S.maps w.prev) (S.maps w.next)).native; let g:= (lastChannel (S.maps w.prev) (S.maps w.next)).native
 let K:= (P).line;let V:= logHeat K ((P).jVac (T.bulk w.prev)) false
 have hx:Cluster.Bill (Cluster.present f A) p:=fun i hi j=>ne_top_of_le_ne_top (h i hi j) (Stalk.quota_collect _ _ _); have hv: Price (markHeat K V (Cluster.present f A)) p:= (H.fund (b:=k) le_rfl).solution w _ hx
 obtain ⟨t,ht,Ht⟩:= H.solid (b:=k) le_rfl
 let s:= lowest (Foot G⊕ Foot G)
 intro i hi j;let Z:= endHeat m K V (Cluster.present f A) i j; let x:=draft (P).driftL Z
 have hh : quota Z 1≠⊤:= packable (Finset.range (m+3*i+1)) _ fun n _ => hv n i hi j
 have hp: Layer.row (Function.swap ((P).driftL)) s id id (t w):= Layer.row_mono (fun a b=>(S.ceilingRoom.cone k w).unit a b) (Ht w).2
 have he: quota x 1≠⊤:=by rw [← lowest_price]; apply ne_top_of_le_ne_top _ (show markQ (Premium.free s) x ≤ markQ (Premium.free s) Z*(t w)^j from mark_draft hp Z); unfold s; rw [lowest_price]; exact ENNReal.mul_ne_top hh (ENNReal.pow_ne_top (ht.cost _)) -- draft inequality
 exact ne_top_of_le_ne_top he (quota_restrict (acrossT g) (injectT g) x 1)
end Transmission
end YM.RegulatorIR.Sources
