import YM.RegulatorIR.Cluster.Calls

/-! Exact change of sign in cover mark reports (only through output order).
Assumes workday & primitive absolute moment finiteness in forms actually
needed. Does not assume the transmission estimate. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Collapsed Composite
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W Z:Type}{X Y V U : W→Type} {p i u n a b k e:ℕ}{L:Meter W}{T Q:Orders Z}

def Aligns (T Q:Rhythm Z)(p k:ℕ): Prop:= ∀ i ≤ p,∀ j≤ k,T j i=Q j i

lemma root_joins {T S Q: Rhythm Z}(h:Aligns T Q p k)(K:Layer Z Z)(he:e≤p): Root T S K k e=Root Q S K k e:=by
 ext1 r;unfold Root; rw [h e he k le_rfl]; apply congr_arg; unfold drift carry; apply Finset.sum_congr rfl;intro t ht;apply Finset.sum_congr rfl; intro s hs; have hx:= Finset.mem_antidiagonal.mp ht;have hv:= Finset.mem_antidiagonal.mp hs; rw [h s.1 (by omega) t.1 (by omega)]
lemma markMinus (T Q: Orders Z)(V: Rhythm Z) {K:Layer Z Z}{M:Tariff Z}{t:ℝ≥0∞}(h:Price (markHeat K V T) p)(hh:Price (markHeat K V Q) p)(hq:Cost V p)(hc:row K M id id t)(hα:t≠⊤)(k:ℕ)(he:e≤p): markHeat K V (T-Q) k e=markHeat K V T k e-markHeat K V Q k e:=by
 induction k using Nat.strong_induction_on generalizing e with
 | _ k ih=>
   cases k with
   | zero=>simp_rw [markHeat_first];rfl
   | succ k=>
     let g (T:Orders Z):= markHeat K V T
     have hx: Aligns (g (T-Q)) (g T - g Q) p k:=fun i hi j hj=> ih j (by omega) hi
     have hz (T:Orders Z) : markHeat K V T (k+1) e=((k+1:ℝ)⁻¹) • Root (g T) V K k e:=funext fun _=> markHeat_next ..
     rw [hz,hz,hz,root_joins (S:=V) hx K he, root_minus h hh hq hc hα he,smul_sub]
lemma heatMinus {T Q: Orders Z} {V: Rhythm Z} {K:Layer Z Z}{M:Tariff Z}{t:ℝ≥0∞}(h:Price (markHeat K V T) p)(hh: Price (markHeat K V Q) p)(hq:Cost V p)(hc: row K M id id t)(hα:t≠⊤)(he:e≤p) : endHeat a K V (T-Q) e = endHeat a K V T e-endHeat a K V Q e:=by
 ext1 i; rw [Pi.sub_apply]; unfold endHeat heated; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _=>congr_fun (markMinus T Q V h hh hq hc hα j he) i)
lemma offer_minus (f:W↪Z) (T S:Orders W): present f (T-S) = present f T-present f S:=by
 ext1 k;ext1 e;ext1 z; by_cases hz:z∈ Set.range (acrossT f)
 · obtain ⟨b,rfl⟩:=hz; change offer f _ _=offer f _ _ - offer f _ _; rw [offer_eq,offer_eq,offer_eq]; rfl
 change offer f _ _=offer f _ _ - offer f _ _; rw [offer_zero _ hz,offer_zero _ hz,offer_zero _ hz,sub_self]

-- Pointwise in layouts. Finite Quota on inputs used, no uniform estimate here.
lemma pointPays {R:Type}{H:Tariff R}(L: Meter Unit)(B: Premium H){j:ℕ}(T:Packet R j)(h: markQ B T ≠ ⊤): Claim L (I:=fun _:Unit=>R) (fun _=>B) 1 (fun _=>T):= Carry.regular (Poly.standard _ h)
-- remove extraneous c param

def lowest (X:Type):Tariff X:= {road:= fun _ _=>1, unit:=fun _ _=>le_rfl, own:=fun _=>rfl, symm:=fun _ _=>rfl, tri:=fun _ _ _=>by simp }
lemma lowest_price (T:Packet W k): markQ (Premium.free (lowest W)) T=quota T 1:= by unfold markQ; apply congr_arg; ext1 w; apply le_antisymm _ (Premium.width_unit ..); apply Premium.width_le; exact Tariff.diameter_le _ le_rfl (fun _ _=>le_rfl); exact fun _=>le_rfl
lemma Fund.solution {l:W → ℝ}{hl:∀ w,0<l w}{x:(w:W)→ X w→ Room}{K: (w:W)→Layer (X w) (X w)}{V:(w:W)→Orders (X w)} (F:Fund p L hl x u V K) (w:W)(T:Orders (X w)) (h:Bill T p): Price (markHeat (K w) (logHeat (K w) (V w) false) T) p:=by
 let g(_:Unit):=w;let L':= L.us g
 let B:=lowest (X w); let A(_:Unit):= B
 have hx:Folds p L' (X:=fun _:Unit=> X w) (fun _=>Premium.free B) 1 (fun _=>T):= fun i hi j=>pointPays L' (Premium.free B) (T i j) (by unfold B; rw [lowest_price];exact h i hi j)
 obtain ⟨f,hf,hα⟩:= Beam.us F.beam g
 have he a b : B.road a b ≤ (home hl x u w).road a b:= (home hl x u w).unit a b
 have hh:Beam L' A (fun _=> K w):=⟨f,hf,fun v=>⟨row_mono he (hα v).1,row_mono he (hα v).2⟩⟩
 have hp i (hi:i ≤ p) j: Workday L' A fun _=>V w i j:=by
    obtain ⟨r,hr,ht⟩:=(F.work i hi j).us g; refine ⟨r,hr,fun v k a=> le_trans ?_ (ht v k a)⟩; apply quota_mono (fun y:Hold k a=>V w i j y.val);intro z; exact Tariff.diam_mono he z.val
 intro k; exact Folds.pay (stays _ hx hh (fun _=>F.vac w) hp false k) (fun _=>ENNReal.one_ne_top) ()
variable (F:Batch X Y V U)(C:(w:W)→Orders (X w)){l:W→ℝ}{hl:∀ i,0<l i}(G:Fund p L hl (Zone F) u (now F C) F.lineL) (H:Beam L (home hl (Zone F) u) F.forecast)
include H G
lemma each_minus {A B:(w:W)→Orders (X w)} (w:W)(h:Bill (A w) p)(hh: Bill (B w) p)(he:e≤p): (F.grid w).each n (C w) (A w-B w) e=(F.grid w).each n (C w) (A w) e - (F.grid w).each n (C w) (B w) e:=by
 let f:= (firstChannel (F.fine w) (F.coarse w)).native; let t:= (lastChannel (F.fine w) (F.coarse w)).native
 let K:=F.lineL w; let V:=logHeat K (now F C w) false; let Λ:= F.forecast w
 have ht (T:Orders (X w))(h:Bill T p): Price (markHeat K V (present f T)) p:= by
    refine G.solution _ _ (fun i hi j=> ?_); exact ne_top_of_le_ne_top (h i hi j) (Stalk.quota_collect _ _ _)
 obtain ⟨c,hc,Hc⟩:= G.beam; obtain ⟨b,hb,Hb⟩:= H
 ext1 i
 let Q:=endHeat n K V (present f (A w)); let P:=endHeat n K V (present f (B w))
 have hP (T:Orders (X w))(h:Bill T p): quota (endHeat n K V (present f T) e i) 1≠⊤:=packable (Finset.range (n+3*e+1)) _ (fun k _=> ht T h k e he i)
 change crop t (draft Λ (endHeat n K V (present f _) e i))=crop t (draft Λ (Q e i)) -crop t (draft Λ (P e i))
 rw [offer_minus,heatMinus (ht (A w) h) (ht (B w) hh) (G.controls w false) (Hc w).1 (hc.cost w) he, Pi.sub_apply,draft_minor _ (hb.cost w) (row_to_sup (Hb w).1) _ _ (hP _ h) (hP _ hh)];rfl
end YM.RegulatorIR.Cluster
