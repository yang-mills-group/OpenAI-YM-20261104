import YM.RegulatorIR.Cluster.Width

/-! Uniform costs across layouts. at this stage directly in ENNReal and no
countability/regularity assumption on layout. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Set Function Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Diagram Collapsed
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W Z : Type} {X Y: W→Type} {L:Meter W}
  {v z:W→ℝ≥0∞} {S T: W→Set Room} {d l:W → ℝ} {hl:∀ w,0<l w} {x:(w:W)→X w→ Room}
  {P Q V:(w:W)→Orders (X w)} {p k e i r a b u:ℕ}

lemma ticket_times {X Y A B:W→ℝ≥0∞}(h:Carry L X A)(hh:Carry L Y B) : Carry L (fun w=> X w*Y w) (fun w=> A w*B w):=by obtain ⟨c,hc,H⟩:=h; obtain ⟨d,hd,G⟩:=hh; refine ⟨_,hc.mul hd, fun w=>?_⟩; exact (mul_le_mul' (H w) (G w)).trans_eq (mul_mul_mul_comm ..)

-- in fine use l most arguments l<=1

def estate (hl:∀ w,0<l w) (x:(w:W)→X w→Room)(S:W→Set Room) (u:ℕ)(w):= (realm (hl w) u (S w)).uses (x w)
def home (hl:∀ w,0<l w)(x:(w:W)→ X w→Room)(u:ℕ) w:= (native _ (hl w) u).uses (x w)

def Folds (p:ℕ) (L:Meter W){A:(w:W)→Tariff (X w)} (H:(w:W)→Premium (A w))(v:W→ℝ≥0∞)(T:(w:W)→Orders (X w)):Prop:=∀ i≤p,∀ r, Claim L H v fun w=>T w i r
variable {K:(w:W)→Layer (X w) (X w)}
lemma lesser (u:ℕ){r:ℕ}{Z:(w:W)→Packet (X w) r}(h:∀ w,(S w).Nonempty)(hh:∀ w,S w⊆T w)(H:Claim L (estate hl x S u) v Z): Claim L (estate hl x T u) v Z:= Carry.mono H fun w=>quota_mono _ fun z=>regions (hl w) u (S w) (T w) (hh w) (h w) (x w) z
lemma tower {q:ℕ}{Z:(w:W)→Packet (X w) r}(he:u≤q)(H:Claim L (estate hl x S q) v Z): Claim L (estate hl x S u) v Z:=by
 apply Carry.mono H; intro w; apply quota_mono;intro z; exact highest _ _ _ _ _ _ ((estate hl x S q w).width_unit _) fun i=> le_trans (moment_mono (hl w) he Metric.infDist_nonneg) ((estate hl x S q w).width_ge z i)
lemma Folds.lesser (u:ℕ)(h:∀ w,(S w).Nonempty)(hh:∀ w,S w⊆T w)(H:Folds p L (estate hl x S u) v P):Folds p L (estate hl x T u) v P:=fun i hi r=> Cluster.lesser u h hh (H i hi r)
lemma Folds.tower (he:u ≤ b)(H:Folds p L (estate hl x S b) v P): Folds p L (estate hl x S u) v P:=fun i hi r=>Cluster.tower he (H i hi r)
lemma Folds.crop {A:∀ w,Tariff (X w)}{B:(w:W)→Premium (A w)}(f:(w:W)→Y w↪X w)(H:Folds p L B v P): Folds p L (fun w=>(B w).uses (f w)) v fun w i r=> crop (f w) (P w i r) := fun i hi r=>Carry.mono (H i hi r) (fun w=>quota_restrict (acrossT (f w)) (injectT _) ..)
lemma Folds.offer {A:∀ w,Tariff (Y w)}{B:(w:W)→Premium (A w)}(f:(w:W)→X w↪Y w)(H:Folds p L (fun w=>(B w).uses (f w)) v P):Folds p L B v fun w i j=> offer (f w) (P w i j) := fun i hi r=> Carry.mono (H i hi r) (fun _=> Stalk.quota_collect ..)
lemma Folds.sub {A:∀ w,Tariff (X w)}{B:(w:W)→Premium (A w)}(h:Folds p L B v P)(hh:Folds p L B v Q): Folds p L B v fun w i r=> P w i r-Q w i r:=fun i he r=> (h i he r).sub (hh i he r)
lemma Folds.times (A:Folds p L (estate hl x S u) v P)(B:Folds p L (estate hl x S u) z Q) : Folds p L (estate hl x S u) (fun w=>v w*z w) fun w=> accord (P w) (Q w):=by
 intro i hi r; unfold accord crisp;apply Claim.sum;intro j hj;apply Claim.sum; intro m hm
 rw [← Finset.mem_antidiagonal.mp hm]; simp only [pie]; have he:=Finset.mem_antidiagonal.mp hj
 exact Carry.mono (ticket_times (A j.1 (by omega) m.1) (B j.2 (by omega) m.2)) fun w=>packet_pair (hl w) u (S w) (x w) _ _
lemma shorter (S:W→Set Room) (h:u≤b)(H:Beam L (home hl x b) K): Beam L (fun w=>(fare (hl w) u (S w)).uses (x w)) K:=by
 obtain ⟨f,hf,F⟩:=H
 have he w (i j:X w) : ((fare (hl w) u (S w)).uses (x w)).road i j ≤ (home hl x b w).road i j:= (lip (hl w) u (S w) (x w i) (x w j)).trans (moment_mono (hl w) h dist_nonneg)
 exact ⟨f,hf,fun w=> ⟨Layer.row_mono (he w) (F w).1, Layer.row_mono (he w) (F w).2⟩⟩
lemma overnight (S:W→Set Room){T:(w:W)→Packet (X w) r}(h:u≤b)(H:Workday L (home hl x b) T):Workday L (fun w=>(fare (hl w) u (S w)).uses (x w)) T:=by
 obtain ⟨f,hf,F⟩:=H
 refine ⟨f,hf,fun w i j=> le_trans ?_ (F w i j)⟩
 apply quota_mono (fun y:Hold i j=>T w y.val); intro z; exact Tariff.diam_mono (fun a b=> (lip (hl w) u (S w) (x w a) (x w b)).trans (moment_mono (hl w) h dist_nonneg)) z.val
variable {A:∀ w,Tariff (X w)} {H:(w:W)→Premium (A w)}
lemma Folds.pay (B:Folds p L H v P) (h:∀ w,v w≠ ⊤) (w): Bill (P w) p := fun i he r=> ne_top_of_le_ne_top (Claim.cost (B i he r) _ (h w)) (quota_mono _ (fun u=> (H w).width_unit u))
lemma stays_mark {C: (w:W)→ Rhythm (X w)} (K:∀ w,Layer (X w) (X w)) (B:Folds p L H v P) (hK:Beam L A K) (hV:∀ i ≤ p, ∀ j k,0 < j → Workday L A (fun w=> C w k i j))(hh:∀ w j k,C w k 0 j=0)(k:ℕ): Folds p L H v (fun w=> markHeat (K w) (C w) (P w) k):=by
 cases k with
 | zero=> simp_rw [Diagram.markHeat_first];exact B
 | succ k=> exact fun i he j=> Claim.total_mark P hK hV (fun w k i=> hh w _ _) (fun i hi j _=>B i hi j) (k+1) i j he (by omega)
lemma stays {U:(w:W)→ Orders (X w)}(K:∀ w,Layer (X w) (X w))(B:Folds p L H v P)(hK:Beam L A K)(hh:∀ w,Vacuum (U w))(hV:∀ i ≤ p,∀ r,Workday L A (fun w=> U w i r))(f:Bool)(k:ℕ): Folds p L H v fun w=>markHeat (K w) (logHeat (K w) (U w) f) (P w) k:= by
 refine stays_mark K B hK (fun i hi j k _=> Workday.hot hV hK f k i j hi) (fun w i k=>Classical.byContradiction (fun hp=>lt_irrefl _ (heated_cap (K w) (U w) (hh w) _ 0 i k hp).1)) k
lemma stays_end {U:(w:W)→Orders (X w)}(K:∀ w,Layer (X w) (X w))(B:Folds p L H v P)(hK:Beam L A K)(hh:∀ w,Vacuum (U w))(hV:∀ i≤p,∀ r,Workday L A (fun w=> U w i r))(f:Bool)(m:ℕ): Folds p L H v fun w=>endHeat m (K w) (logHeat (K w) (U w) f) (P w):=fun i hi r=> Claim.sum _ (Finset.range (m+3*i+1)) fun k _ => stays K B hK hh hV f k i hi r
end YM.RegulatorIR.Cluster
