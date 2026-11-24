import YM.OPE.Coverage.Producer
/-! ## Dense weak shelves even for arbitrary prescribed length paths (comparison radii within polylog factors) -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Function Filter Set Lattice Wilson RG Precision Next.Rank Station Extraction Next.UVStress Climb
open Topology Real MeasureTheory
open Cells Next.Rank.East MergeProof.East
open scoped Topology
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{L:Levels G}{r p:ℕ→ℝ}
def mark(r:ℕ→ℝ)(i:ℕ):=-Real.log (r i)
def Fine (r:ℕ→ℝ):= (∀ i,0<r i) ∧ Tendsto (mark r) atTop atTop
-- remove dummy
def Close(r p:ℕ→ℝ):= (∀i,0<p i)∧ ∃ c:ℝ,0 < c ∧ ∀ᶠ k in atTop, |mark r k - mark p k|≤ c*log (1+mark r k)
set_option quotPrecheck false
local notation "Y" => L.S.scale
private theorem crest_set (s:ℝ):∃ k, s≤ Y k:= by exact (L.S.divergent.eventually_ge_atTop s).exists
-- shadow fix
private def crest (A:Levels G) (s:ℝ) := Nat.find (show ∃ k,s≤ A.S.scale k from crest_set (L:=A) s)

lemma crest_grows (A:Levels G): Tendsto (crest A) atTop atTop:= tendsto_atTop_atTop.mpr fun m=> ⟨1+A.S.scale m,fun s hs=> lt_of_not_ge (fun h=>by have he:s ≤ A.S.scale m :=le_trans (show s ≤ A.S.scale (crest A s) from (Nat.find_spec (p:=fun k=>s≤ A.S.scale k) (crest_set s))) (scales_route A h); exact (not_le_of_gt (by linarith only [hs])) he) |>.le ⟩

lemma exist_grid (L:Levels G)(hL: ∀ᶠ i:ℕ in atTop,Real.log ((L.S.block i).val:ℝ) ≤ Real.log (1+L.S.scale (i+1))) : ∃ k:ℝ→ℕ, Tendsto k atTop atTop ∧ ∀ᶠ s in atTop, |L.S.scale (k s)-s| ≤ log (1+L.S.scale (k s)) ∧ log (1+L.S.scale (k s))≤ 2*log (1+s):= by
    -- no lattice mesh limit exchanged here
    let k:= crest L; have hk :=crest_grows L
    have hm : Tendsto (fun s=>k s -1) atTop atTop:= by
         refine tendsto_atTop_atTop.mpr (fun m=>?_)
         obtain ⟨i,hi⟩:=eventually_atTop.1 (hk.eventually_ge_atTop (m+1))
         exact ⟨i,fun s hh=> by have h:=hi _ hh; change m ≤ (crest L s)-1; omega⟩
    refine ⟨_,hk,?_⟩
    filter_upwards [hm.eventually hL,(L.S.divergent.comp hk).eventually (log_speed 1 one_pos), eventually_gt_atTop (0:ℝ)] with s hl hk hs
    have hPos:k s ≠ 0:= by
        intro ht; have hx:=Nat.find_spec (p:=fun i=>s≤L.S.scale i) (crest_set s)
        change _≤L.S.scale (k s) at hx; rw [ht,L.S.scale_zero] at hx; linarith
    rcases ht:k s with _|t
    · exact (hPos ht).elim
    change _≤_ ∧ _≤_ at hk
    have hy : s ≤ L.S.scale (t+1):= ht ▸ (show s ≤ L.S.scale (k s) from Nat.find_spec (p:=fun i=>s ≤ L.S.scale i) ..)
    have he : k s-1=t:=by omega
    have hz:L.S.scale t< s:=lt_of_not_ge (Nat.find_min (p:=fun i=>s ≤ L.S.scale i) _ (show t < k s from by omega))
    have hu : L.S.scale (t+1) ≤ 2*s:=by
          have ha:=L.S.scale_succ t
          dsimp only [Function.comp_apply] at hk; change _ ≤ _ at hl
          rw [show crest L s=k s from rfl,ht] at hk
          have hl:= (show Real.log ((L.S.block (k s-1)).val:ℝ) ≤ Real.log (1+L.S.scale (k s-1+1)) from hl)
          rw [he] at hl
          linarith only [hz,hl, L.S.scale_succ t,hk.1,hk.2]
    constructor
    · rw [← show k s=crest L s from rfl,ht,abs_of_nonneg (sub_nonneg.mpr hy)]
      have hl:= (show Real.log ((L.S.block (k s-1)).val:ℝ) ≤ Real.log (1+L.S.scale (k s-1+1)) from hl); rw [he] at hl
      linarith only [hl,L.S.scale_succ t,hz]
    rw [← show k s=crest L s from rfl,ht, show 2*log (1+s)=log (1+s)+log (1+s) from two_mul _,← Real.log_mul (show 1+s≠0 by linarith) (by linarith only [hs])]
    exact Real.log_le_log (by linarith only [hy,hs]) (by nlinarith only [hu,sq_nonneg s])

-- preserve ALL old balances with changed index map, no new periods.
private lemma invoc {n d R a}{w:ℕ→Wheel C d}(h:Granular w F R n a)(p:ℕ→ℕ)(hp:Tendsto p atTop atTop):Granular (w∘p) F R n a where
   grants:= hp.eventually h.grants
   real:=hp.eventually h.real
   h_symm:=hp.eventually h.h_symm
   central:=hp.eventually h.central
   small:=h.small.comp hp
   proof_ k hk m hm x:= by
        obtain ⟨e,A,B,h'⟩:= h.proof_ _ hk _ hm x; rcases h' with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        exact ⟨e∘p,A∘p,B∘p,h1.comp hp,h2.comp hp,hp.eventually h3,hp.eventually h4,h5.comp hp,h6.comp hp,hp.eventually h7⟩
private lemma roomer {F:Extraction.Order}{n:ℕ}{w:ℕ→Wheel C n}(h:Levy.Lodged F w)(p:ℕ→ℕ)(hp:Tendsto p atTop atTop):Levy.Lodged F (w ∘p):=by
   obtain ⟨z,c,h1,h2,h3,h4,h5,h6⟩:= h
   exact ⟨z∘p,fun d=>c d ∘ p,h1.comp hp,h2.comp hp,h3.comp hp,fun d=>(h4 d).comp hp,fun d i=>h5 ..,fun d i=> h6 ..⟩

theorem paid_on_demand (h:Paved C F)(hr:Fine r):(∀ i≥1,∀t:ℕ,∀ s:ℝ,s>0 → (standard C).Smooth → ∀ a:(Bel C.book).RealSpin,
           ∃ w:ℕ→Wheel C t,Close r (fun i=>(w i).r) ∧ Levy.Lodged F w ∧ Granular w F a i s ∧ Stripe w):=by
     rintro i - t s hs hQ a
     obtain ⟨hv,hR⟩:= hr
     obtain ⟨k,hk,hA⟩:= exist_grid C.path.levels h.stride
     obtain ⟨w,hw₀,h',⟨κ,hκ,hp,hcost⟩,hP⟩:= h.demand i t s hQ a hs
     let f:=k ∘ mark r; have hf:Tendsto f atTop atTop:=hk.comp hR
     refine ⟨w∘f,⟨fun i=>(w (f i)).rad,2*κ+2,by linarith only [hκ],?_⟩,roomer h' f hf,invoc hw₀ f hf, ⟨fun p hp=> hf.eventually (hP.rate p hp)⟩⟩
     filter_upwards [hf.eventually hcost, hR.eventually hA] with i hi hr
     let y:= C.S.scale (f i); let x:=mark r i; let a:=mark (fun i=> (w (f i)).r) i
     have ht: |a-y| ≤ κ*log (1+y):=(show _ ≤ _ from (abs_neg (a-y)) ▸ (show |-(a-y)| ≤ _ from (by dsimp only [a, y, mark]; rwa [neg_sub,sub_eq_add_neg,neg_neg,add_comm])))
     change |y-x| ≤ log (1+y) ∧ log (1+y) ≤ 2*log (1+x) at hr
     have hb:log (1+y) ≤ 2*log (1+x):=hr.2
     exact (show |x-a| ≤ |y-x|+|a-y| by rw [show x-a= -((y-x)+(a-y)) from by abel,abs_neg]; exact abs_add_le ..).trans (by nlinarith only [hr.1,ht,mul_le_mul_of_nonneg_left hb hκ.le,hb])
end YM.OPE.Coverage
