import YM.FormalBulk08.North.Wing

/-! Local reset and Civic-through. Kernel selection may give unplotted values at
ANY higher horizon; output independent of such values. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I J:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E e r:ℕ}{W:Lab G K I}
variable (a:hue G)(hp:Use W ρ E)(h:LocalRatio ρ)(hs:G.Simple)(x:Leaf W.scrolls)
include hp h hs
lemma madrid (he:e≤E)(r:ℕ):
    Totem staticT (fun _=> fame _) (fun _=> W.windowD x) (coinR x) (fun n=>eating ρ a W (fun _=>seqN x n) x.a x.b e r) (fun _=> crest ρ a x (heir a ρ W x.a (x.b+1)) e r):= by
    by_cases he': e=0
    · subst e
      have hh n: eating ρ a W (fun _=>seqN x n) x.a x.b 0 r= saga ρ a W x.a (seqN x n) x.b 0 r:= by
          unfold saga; rw [through _ _ _ _ _ (seqN x n) x.b (by unfold seqN;omega)]; symm; exact paid_nil _ _ _ _ (book_fresh _) (book_guard _)
      obtain H:= totem_hold (r:=r) a hp h hs x he; have hv:= H.links (fun n:ℕ=>n+1); have hP i: fare_n x (i+1+x.b) ≤ coinR x i:= by
          let S:= (W.V x.a).S; change ratioR S _ _ _≤ratioR S (seqN x i) (x.b+1) _; rw [show i+1+x.b=seqN x i by unfold seqN;omega]; unfold ratioR; gcongr
          all_goals first|exact targetPower_pos.le|exact S.strictAnti.antitone (Nat.le_succ _)|exact S.a_pos _|exact (S.a_pos _).le|exact div_nonneg (S.a_pos _).le (S.a_pos _).le
      simp_rw [hh]; convert hv.wanes (D:=coinR x) hP using 1
      all_goals first|rfl| ext1 i; rw [seqN,show i+(x.b+1)=i+1+x.b by omega]
      -- defeq crest0?
    by_cases hr:r=0
    · subst r
      simp only [eating,waken,if_neg he',crest,↓reduceIte]; apply Aster.voids
    exact summits a x hp h hs he (by omega) (⟨0,(by omega)⟩ : Fin r)

-- through e order computations
omit hp h hs
def haloO (ρ:ChartRatio G)(a:hue G)(x:Leaf W.scrolls): Pence:= scalar a (crest ρ a x (heir a ρ W x.a (x.b+1)))
include hp h hs
omit hp in
lemma sunlight (i:ℕ): Fresh (scalar a (eating ρ a W (fun _=>seqN x i) x.a x.b)):= by
    let p:transferPoint W:=⟨x,seqN x i,seqN x i,by unfold seqN;omega,le_rfl⟩; exact (pesto h a hs p _ p.wing).1
lemma solar : Priced staticT (coinR x) (fun n=> scalar a (eating ρ a W (fun _=>seqN x n) x.a x.b)) (fun _=> haloO ρ a x) E := by
    intro n hn; simp only [haloO,scalar,coeff_mk]; exact teller_pay a (soft_coin _ _) (fun _=> (W.turn_quota hp x).price) (fun _=> hp.zero x) (madrid a hp h hs x hn 2)
lemma freshK : Fresh (haloO ρ a x):= by
    apply tendsto_nhds_unique (quietP (coinD x) (coinP x) (solar a hp h hs x 0 (Nat.zero_le E))); exact tendsto_const_nhds.congr' (.of_forall fun n=> (sunlight a h hs x n).symm)
lemma divisionC (he:e≤ E) : Ends (fun N=> coeff e (scalar a (eating ρ a W (fun _=>N) x.a x.b))) (coeff e (haloO ρ a x)):= (tendsto_add_atTop_iff_nat _).1 (quietP (coinD x) (coinP x) (solar a hp h hs x _ he))
lemma sanctuary (he:e≤ E)(r:ℕ) : Totem staticT (fun _=> fame _) (fun _=> W.windowD x) (coinR x) (fun n=> saga ρ a W x.a (seqN x n) x.b e r) (fun _=>Wine.normalized a (crest ρ a x (heir a ρ W x.a (x.b+1))) e r):= by
    obtain ⟨hB,hU⟩:= (solar a hp h hs x).goods (sunlight a h hs x) (fun _=> freshK a hp h hs x); let T n:=eating ρ a W (fun _=>seqN x n) x.a x.b
    have hv N: saga ρ a W x.a (seqN x N) x.b = Wine.normalized a (T N):= through _ _ _ _ _ _ x.b (by unfold seqN;omega)
    simp_rw [hv, normalized, stamp]; apply totem_sums _; intro i hi; rw [Finset.mem_range] at hi; exact (madrid a hp h hs x (show i≤E by omega) r).amp (hB.income hU _ _ _ (by omega))
lemma continuation (he:e≤ E) : heir a ρ W x.a x.b e=Wine.normalized a (crest ρ a x (heir a ρ W x.a (x.b+1))) e := by
    have hv:=North.crown a hp h hs he; ext r v; cases r with
    | succ r=> exact tendsto_nhds_unique ((hv _ x).shares v) ((static_serene (p:=fun n=> saga ρ a W x.a n x.b e (r+1)) (x.b+1) (stillK 0 (hp.zero x).le (coinD x) (coinP x) (sanctuary a hp h hs x he (r+1)))).shares v)
    | zero=>
       have he' : ∀ j≤ E,heir a ρ W x.a x.b j 0=0:= fun j hj=>by
           have ht': stopper (heir a ρ W x.a x.b) E j 0=0:= by by_contra H; have hx:= ((born a x hp h hs).valence _ _ H).1;omega
           simpa [stopper,hj] using ht'
       let U:= crest ρ a x (heir a ρ W x.a (x.b+1)); rw [he' _ he]; change (0:Tile (edgeL G) 0) _= Wine.normalized a U e 0 _
       have hp: Wine.normalized a U e 0=0:= by
           unfold Wine.normalized stamp; apply Finset.sum_eq_zero; intro i hi; unfold U crest; by_cases ht:i=0
           · rw [ht]; simp only [↓reduceIte]; rw [he' 0 (Nat.zero_le _),smul_zero]
           simp only [ht,↓reduceIte,smul_zero]
       rw [hp]
end YM.FormalBulk08.North
