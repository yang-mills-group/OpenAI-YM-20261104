import YM.MS.ScaleForest.Profit
/-!
# Base trees from joining two named lists of possible children (observer identities)

Costs for building the three recursive source shapes. No assumption made
about the graphs other than the concrete occurrence/Standing hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J M: Type}

-- cusp pulls two list sums if good
local notation "C"=> (Curtain G I)
private theorem bill_once (l:List J)(u:J→C) (A:C→ Glade G I) (he:A 0=0) (hx:∀ F H, Seen F→Seen H→ A (F+H)=A F+A H)(h:∀ i∈l, Seen (u i)) :
    (l.map (A∘u)).sum=A (l.map u).sum∧ Seen (l.map u).sum:= by
   induction l with
   | nil=> exact ⟨he.symm,Seen.zero⟩
   | cons i l ih=> obtain ⟨hr,hP⟩:= ih fun j hj=> h j (List.mem_cons_of_mem _ hj); simp only [List.map_cons,List.sum_cons,Function.comp_apply, hr,hx _ _ (h i (by simp)) hP]; exact ⟨ trivial, Seen.add (h i (by simp)) hP⟩
structure twoBill (U: C→C → Glade G I) : Prop where
   right F: Seen F→ U F 0=0
   left F: Seen F→ U 0 F=0
   onRight F G H: Seen F→ Seen G→ Seen H→ U F (G+H)=U F G+U F H
   onLeft F G H: Seen F→ Seen G→ Seen H→ U (G+H) F=U G F+U H F

lemma twoBill.project (l:List J)(r:List M)(u:J→C)(v:M→C)(U:C→C → Glade G I)(h:twoBill U)(hp:∀ i∈l,Seen (u i))(hr:∀ i∈r,Seen (v i)) :
    (expandsTwo (fun i j=> U (u i) (v j)) l r).sum= U (l.map u).sum (r.map v).sum := by
   have hv : Seen (r.map v).sum:= Seen.list (by intro i hi; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hi; exact hr j hj)
   induction l with
   | nil=> exact (h.left _ hv).symm
   | cons i l ih=> obtain ht : ∀ j∈l, Seen (u j):= fun j hj=> hp j (List.mem_cons_of_mem _ hj); obtain hx:= hp i (by simp);
                    have hl:Seen (l.map u).sum:=Seen.list (by intro i hi; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hi; exact ht j hj); unfold expandsTwo; rw [ List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons ];
                    rw [h.onLeft _ _ _ hv hx hl, ← ih ht]; exact congr_arg₂ (·+·) (bill_once r v _ (h.right (u i) hx) (fun X Y=> h.onRight (u i) X Y hx) hr).1 rfl

lemma pinpoint_bill (K:LineRule G)(μ:ℝ)(v:I→QP): twoBill (fun X Y=> projectV 0 (Pfor K μ X Y v)) := by
   constructor
   · intro X _; apply Eq.trans (projects _ (X:=Pfor K μ X 0 v) (Y:=0) (funext fun s=> funext fun i=> emptyPin_r (F:= (0:Mob G)) (show Goods 0 _ from (good ..).zero_mem) 0 _ _)); exact map_zero ..
   · intro X _; exact (projects _ (X:=Pfor K μ 0 X v) (Y:=0) (funext fun s=> funext fun i=> emptyPin_l (F:= (0:Mob G)) (show Goods 0 _ from (good ..).zero_mem) 0 _ _)).trans (map_zero (projectV 0))
   · intro X Y Z hx hy hz; exact (projects 0 (Y:=Pfor K μ X Y v+Pfor K μ X Z v) (X:=Pfor K μ X (Y+Z) v) (funext fun s=> funext fun i=> pinPlus2 K pit (hy i s) (hz i s) (hx i s) _ _)).trans (map_add ..)
   intro X Y Z hx hy hz; exact (projects 0 (Y:=Pfor K μ Y X v+Pfor K μ Z X v) (X:=Pfor K μ (Y+Z) X v) (funext fun s=> funext fun i=> pinPlus1 K pit (hy i s) (hz i s) (hx i s) _ _)).trans (map_add ..)
lemma bridge_bill (K:LineRule G): twoBill (I:=I) (fun X Y=> projectV 0 (Bfor K X Y)):= by
   let f:=Bfor (I:=I) K; constructor
   · intro X _; rw [show Bfor K X 0=0 from ?_,map_zero]; funext z s t; simp only [Bfor,Pi.zero_apply,bridgeG_eq K.ok.rev, ← schedule,map_zero];
   · intro X _; rw [show Bfor K 0 X=0 from ?_,map_zero]; funext z s t; simp only [Bfor,Pi.zero_apply,bridgeG_eq K.ok.rev, ← schedule,map_zero,LinearMap.zero_apply];
   · intro X Y Z _ _ _; rw [ ← map_add (projectV 0) ]; apply congr_arg; funext z s t; simp only [Bfor,Pi.add_apply,bridgeG_eq K.ok.rev, ← schedule,map_add]
   intro X Y Z _ _ _; rw [ ← map_add (projectV 0) ]; apply congr_arg; funext z s t; simp only [Bfor,Pi.add_apply,bridgeG_eq K.ok.rev, ← schedule,map_add, LinearMap.add_apply]

lemma expandCarry {A B E F:Type}(X:List A)(Y:List B)(f:A→ B→ E)(g:E→F): (expandsTwo f X Y).map g= expandsTwo (fun i j=>g (f i j)) X Y:= by unfold expandsTwo; simp [List.map_flatMap]; rfl
namespace Planted
variable [TopologicalSpace I] {L:List J} {b c:Bool}
variable (Y : Plan G I b) (F: Plan G I c) (K:LineRule G) (μ:ℝ) (V:Palette G)

lemma hire_twice {L:List J} {Y:List M}(f:J→M→ Planted G I b)(h:∀ i∈L,∀ j∈Y,(f i j).Stand): Hired (expandsTwo f L Y):= by intro i hi; obtain ⟨j,hj,hW⟩:= List.mem_flatMap.mp hi; obtain ⟨k,hk,rfl⟩:= List.mem_map.mp hW; exact h j hj k hk

abbrev Stock (G:Gauge) := List (GraphSum G true 4)
def bulkNom (μ:ℝ)(L:Stock G) : Curtain G I:= (L.map (fun X=> asLeaf X.instructions.renorm μ 0)).sum
def orchard (V:Palette G) (X:Plan G I true) := X.flatMap (fun i=> overline V (i.slots.toNat/2) i)
omit [TopologicalSpace I] in
def grove (μ:ℝ)(L:Stock G) := projectV (I:=I) (-4) (bulkNom μ L)

def Mix (V:Palette G)(L:Plan G I b)(R:Plan G I c)(A:I→QP) : Plan G I true := V.lines.flatMap fun K=> orchard V (expandsTwo (P K A) L R)
def bulkMix (V:Palette G)(F:Plan G I true)(L:Stock G) : Plan G I true:= V.lines.flatMap fun K=> orchard V (expandsTwo (B K) L F)
lemma muster (X:Plan G I true) (ht:Hired X): Hired (orchard V X) := hire_over _ (fun i hi=> lineup V i (ht i hi) _)
lemma hire_pin (hx:Hired Y)(hy:Hired F){A:I→QP}(h:AdmittedGap A): Hired (Mix V Y F A) := hire_over _ (fun _ _=> muster V _ (hire_twice _ (fun i hi j hj=> ⟨ hx i hi,hy j hj,h⟩ )))
lemma hire_b (L:Stock G)(X:Plan G I true)(h:Hired X): Hired (bulkMix V X L):= hire_over _ (fun _ _=> muster V _ (hire_twice _ (fun _ _ j hj=> h j hj)))
variable [FirstCountableTopology I] {q:I→QP}
lemma spread_sum (X:Plan G I true) (h:Hired X) : profit μ (orchard V X)=projectV 0 (interests μ X):= by unfold orchard; rw [profitFlat μ _ (fun i hi=> lineup V i (h i hi) _) ]; unfold interests; rw [map_list_sum,List.map_map]; apply congr_arg List.sum; apply List.map_congr_left; intro i hi; exact daylight μ V i (h i hi) (by omega)
-- combine sums in exact families
local notation "𝒟"=> (constantP G I (PlanetD G))
lemma Mixing (h:AdmittedGap q)(ht:Hired Y)(hp:Hired F): profit μ (Mix V Y F q)=regionC (fun _=>planeF) q 𝒟 (projectV 0 (nominal μ Y)) (projectV 0 (nominal μ F)) := by
   let y (K:LineRule G):= expandsTwo (P K q) Y F; have hy(K:LineRule G): Hired (y K):= hire_twice _ (fun i hi j hj=> ⟨ht i hi,hp j hj,h⟩);
   have hh (K:LineRule G) : profit μ (orchard V (y K))= projectV 0 (Pfor K μ (nominal μ Y) (nominal μ F) q):= by
      rw [spread_sum μ V (y K) (hy K), interests, map_list_sum, List.map_map]; unfold y; rw [ expandCarry]; exact twoBill.project Y F (resolve μ) (resolve μ) _ (pinpoint_bill K μ q) (fun i hi=> sit_seen μ i (ht i hi)) (fun i hi=> sit_seen μ i (hp i hi))
   change profit μ (V.lines.flatMap (fun i=> orchard V (y i)))=_; rw [profitFlat μ _ (fun i hi=> muster V (y i) (hy i))]; simp_rw [hh]; rw [← sensingP V μ (co_visible μ Y ht) (co_visible μ F hp), map_list_sum,List.map_map]; rfl
omit [FirstCountableTopology I] in
lemma freshSeen (X:GraphSum G true 4): Seen (I:=I) (asLeaf X.instructions.renorm μ 0):= by obtain ⟨R,hR,hW,hT⟩:= resetBulk (I:=I) X μ 1 zero_lt_one; exact fun x i=> hW.forms _ hR.top i x
lemma bMixing (L:Stock G)(F:Plan G I true)(h:Hired F): profit μ (bulkMix V F L)=expJ 𝒟 (grove μ L) (projectV 0 (nominal μ F)) := by
   let y (K:LineRule G):= expandsTwo (B K) L F; have hy(K:LineRule G): Hired (y K):= hire_twice _ (fun i hi j hj=> h j hj)
   have hh(K): profit μ (orchard V (y K)) = projectV 0 (Bfor K (bulkNom μ L) (nominal μ F)):= by
      rw [spread_sum μ V (y K) (hy K), interests,map_list_sum,List.map_map]; unfold y; rw [expandCarry]; exact twoBill.project L F (fun i=> asLeaf _ _ _) (resolve μ) _ (bridge_bill K) (fun i hi=> freshSeen μ i) (fun i hi=> sit_seen μ i (h i hi))
   unfold grove; change profit μ (V.lines.flatMap (fun i=> orchard V (y i)))=_; rw [profitFlat μ _ (fun i hi=> muster V (y i) (hy i))]; simp_rw [hh]; rw [← sensingB V, map_list_sum,List.map_map]; rfl
end Planted
end YM.MS.ScaleForest
