import YM.FormalBulk08.Palm.Largo

/-! Push polynomial probes (FULL sampled log). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {m d l e n j t D :ℕ}{A B η σ:ℝ}{L: Side}{o:Loc G 1}
lemma slips (s:Seasons)(x:Site L)(hL:2≤L.val)(h:upper s<D)(P:Studio D→ₗ[ℝ]ℝ)(A:ℝ)(hA:0≤A)(he:∀ i:Spring D, upper i.val≤upper s→ ‖P (cone D i.val)‖≤ A) : ‖P (throughW x D hL (cone D s))‖≤ ((upper s+1:ℕ):ℝ)*Fintype.card (Spring D)* (‖cone D s‖*A):= by
    let Q:= ‖cone D s‖*A; have H : 0≤Q:= mul_nonneg (norm_nonneg _) hA; let y:= throughW x D hL (cone D s)
    have hh k (hk:k∈Finset.range (upper s+1)): ‖P (pamphlet y k)‖≤ Fintype.card (Spring D)*Q:= by
       unfold pamphlet; rw [map_sum]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum fun i e=>?_).trans (cardinal k Q H))
       rw [map_smul,norm_smul]; refine mul_le_mul ((notch_le _ y).trans (through_le x hL _)) (he _ ?_) (norm_nonneg _) (norm_nonneg _); have hm:= Finset.mem_range.mp hk
       exact ((Finset.mem_filter.mp e).2).trans_le (by omega)
    rw [flag_built x h hL,map_sum]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum hh).trans_eq ?_); rw [Finset.sum_const, Finset.card_range,nsmul_eq_mul, mul_assoc]
lemma upheave (T:Tile (edgeL G) m)(x:Site L){S:Cross L (Loc G 1) (Loc G 1)}(hs:S.strip η A)(ha:0≤A)(h:η≤ L.val* σ)(hx:0≤η)(ht:Knoxville (fame _) σ (0,o) T B) :
    Knoxville (fame _) η (0,o) (upmost L x S T) (1*((Real.exp (8*η)*B)*(Fintype.card (Loc G 1)*A)^m)):= by
   let t:edgeL G:=(lift x,o); have hz:piz L t o=(0,o):= Prod.ext (show Stationary.rent L (lift x)=0 from (rent_raw _ (lift x) x (by simp)).2) rfl; rw [←hz]; exact penn_prism (fun _:Fin m=>S) t o (fun _=>hs) _ ha (knight _ _ _ ht) h hx
/-- Account on common block length (post). All projections computed preimage-by-preimage. -/
lemma badges (o:Loc G 1)(F:Frame G d)(n l e D q:ℕ)(r:Fin n→ℕ)(hr:∀ i,0<r i)(X: Fin n→ Snap G d)(hw:∀ i,throughSlot (X i) (r i))(v: Seasons)(hv:(∑ i,r i)+upper v < q)
      (hp:d<D)(hq:q≤d+1)(U : Side)(j t:ℕ)(hd:d≤j)(hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:0<σ):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ x:Site P.L,∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Bonds F o σ q e n Y B →(∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)→∀ η A:ℝ,0<η → η ≤ P.L.val * σ → (linesOf P K.penalty).strip η A → 0≤A →
     ‖slate (upmost P.L x (chair P G K) (Y (throughW x D hL (cone D v)) e n)) d n X‖≤ C*B:= by
    let U0 i:=Place.sampled (X i); choose f hf hz using fun i=> analyze (U0 i) (steady_bl _ _ (hw i))
    choose C hC HC using fun i:Fin n=> deliver (E:=G.Color) K.penalty K.penalty_pos hj ht (r i) (show r i ≤ j from (Finset.single_le_sum (f:=r) (fun i _=> Nat.zero_le _) (Finset.mem_univ _)).trans (by omega))
    let a i:= C i* pile (f i); have ha i:0≤a i:=mul_nonneg (zero_le_one.trans (hC i)) (pile_pos _)
    let s:=Finset.univ.filter (fun i:Spring D=>upper i.val≤ upper v)
    choose! c hc Hc using fun (x:Site U)(i:↥s)=> pristine o F (lift x) D q n l e hq i.val.val r H hr (show (∑ j,r j)+upper i.val.val< q from (Nat.add_le_add_left (Finset.mem_filter.mp i.property).2 _).trans_lt hv) hs a ha
    let Y(x:Site U):=∑ i,c x i; have hY x:0≤Y x:= Finset.sum_nonneg (fun _ _=> hc x _); let E:=∑ x:Site U,Y x; have hE:0≤E:=Finset.sum_nonneg fun i _=>hY i
    let D0 := ((upper v+1:ℕ):ℝ) * Fintype.card (Spring D);
    refine ⟨D0*(‖cone D v‖*E),mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (norm_nonneg _) hE),fun P hs' x hL Z HZ B hB hW η A hη he h' hA=>?_⟩
    choose g hg using fun i=>HC i P (f i)
    let L i:=assigns (eastern (charted (g i)) (lift x)); let z:=throughW x D hL (cone D v)
    obtain ⟨a',ha'⟩:=hW z; let T:= Y -- temp dependent
    let b:=upmost P.L x (chair P G K) (Z z e n); change ‖slate b d n X‖≤ _; rw [severance b (pearl_agate (merit (chair P G K)) (jetty_agate _ (HZ.fare.2.1 z e n))) (upheave _ x (grown_budget G _ hA h') hA he hη.le ha') hη]; let W0 i:= charted (g i)
    rw [show tariffs (fun i=> assigns (Place.sampled (X i))) b = tariffs L (Z z e n) from occurs _ ha' hs.le x hη he _ h' hA U0 r (fun i=>steady_bl _ _ (hw i)) W0 (fun i=>?R)]
    swap; · rw [← hz]; exact (hg i).rolled
    let V (p: Studio D):= tariffs L (Z p e n); have hV:IsLinearMap ℝ V:=peer_role o L HZ (fun i=>shoulder (band_shift (read_poly (g i)) _)); let M:Studio D→ₗ[ℝ]ℝ:=⟨⟨V,hV.1⟩,hV.2⟩
    have hz' i (hi: i∈s): ‖M (cone D i.val)‖≤ E*B:= by
        let x': Site U:= hs' ▸ x; have he' : lift x'=lift x:= by subst U; rfl
        let k:↥s:=⟨i,hi⟩; have hh:=Hc x' k Z HZ B hB; obtain ⟨u,hu⟩:= hW (cone D i.val)
        have hU:= hh u hu g (fun i=>reel_norm (hg i) (zero_le_one.trans (hC i))); rw [he'] at hU
        exact hU.trans (mul_le_mul_of_nonneg_right (show c x' k≤E from (Finset.single_le_sum (f:= c x') (fun j _=>hc x' j) (Finset.mem_univ _)).trans (show Y x' ≤ E from Finset.single_le_sum (f:=Y) (fun i _=> hY i) (Finset.mem_univ _))) hB.1)
    rw [mul_assoc D0,mul_assoc ‖cone D v‖ E]; exact slips v x hL (by omega) M (E*B) (mul_nonneg hE hB.1) (fun i hi=>hz' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
end YM.FormalBulk08.Palm
