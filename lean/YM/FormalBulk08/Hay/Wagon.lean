import YM.FormalBulk08.Hay.Corpus

/-! Complete E-template and width symbol. Does not infer pre/post
funding from path construction; separate setup. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{n:Side}{p:Clip}{R:PathData G}{j t m r e E:ℕ}{σ K B Z:ℝ}
-- loop as positive packet only here
lemma loop_budget (hp:R.Bounds p σ K B){V:Pot G} (h:Freeze (t:=1) V R.loop 2) (i:hue G): value i (V 2 2)=0:= by
    let L:= V 2 2; let X:=filing R
    obtain ⟨δ,W,hd,H⟩:= h.fare 2 2
    have hz:= filing_ready R hp; have hx:= pitch L H hd; have hw: ∀ n,Recorded (pixel L) (turnSeries R.loop (m:=n)) 0:= (matched_iff _ _ (h.civil 2 2) H hd.le).mp h.coins
    have ht (a:Corn (Keys 1))(x v) : X x v (axes a)=pixel L x v (axes a):= by
       obtain ⟨Y,u,H,U⟩:= fleet paradeS marching (axes a) (axes_real _)
       exact tendsto_nhds_unique
         (harvest (fun i j=>(hz.1 i j).1) (F:=fun i=>turnSeries R.loop (m:=paradeS i)) (ε:=fun _=>0) (fun i=>by rw [mul_zero]; exact hz.2 _) tendsto_const_nhds a Y u H U x v)
         (harvest hx (ε:=fun _=>0) (F:=fun i=>turnSeries R.loop (m:=paradeS i)) (fun i=>by rw [mul_zero]; exact hw _) tendsto_const_nhds a Y u H U x v)
    let f:= pressLens (pixel L) ![i,i] 1 1
    have hF:Stationary.Rays 4 f:= by
        intro x; unfold f; simp_rw [pressLens,← ht,map_smul]; exact (hz.1 _ _).2 (roads x)
    have he:= lemon L (h.agate 2 2) ⟨δ,W,hd,H⟩ i
    have hh: leapTip (pixel L) (step 0) 1 ![i,i]=0 := ?_
    rw [show leapTip _ _ _ _= _ from hh] at he; simpa using he.symm
    case _=> change Tensor.coeff f 2 0 _=0; unfold Tensor.coeff; rw [(rays_jet (priceL hx _ _ _) 4).mp hF 2 (by omega),smul_zero];rfl
lemma books_neg {T : Pot G}(_: FloatK T)(n:Side): stone (-T) n= -stone T n:= by rw [show -T=(-1:ℝ) • T by rw [neg_one_smul]]; ext1 e; rw [map_neg,sow_coeff,sow_coeff,sow,sow,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [Pi.smul_apply,Pi.smul_apply, cum_smul,map_smul,neg_one_smul]
lemma FloatN {T : Pot G}(h: FloatK T): FloatK (-T):= by
   have hv: Vivid (-T):= by
       refine ⟨fun i j=>?_ ,fun i j=> ?_,fun i j ht=> h.valence i j fun z=>ht (by simp [z])⟩
       · rw [Pi.neg_apply,Pi.neg_apply,←neg_one_smul ℝ];exact Up.smul (h.civil i j) _
       rw [Pi.neg_apply,Pi.neg_apply,←neg_one_smul ℝ];exact (Agate.smul (h.agate i j) _)
   refine { hv with fare:=fun i j=>?_, civic:=fun n=>?_ }
   · obtain ⟨u,C,hh,H⟩:=h.fare i j; exact ⟨u,C,hh,H.neg⟩
   rw [books_neg h]; intro s x I inst a b k ha hb A B hk hu hp; rw [map_neg,map_neg,h.civic n s x I _ _ _ ha hb A B hk hu hp]

-- main packet

def coveBase (T:(r:ℕ)→ Tile (edgeL G) (r+1)):Pot G:=snowcap T 1 0
lemma book_caps {T:(r:ℕ)→Tile (edgeL G) (r+1)}(hp:R.Bounds p σ K B)(ht:∀ r, Matched (T r) (fun n=> intended p R (m:=n)))(h:∀ r,Up (T r)){A W:ℕ→ℝ}(hv:∀ r,0<W r)(hh:∀ r,Bail (fame _) (W r) (T r) (A r)) (hS:G.Simple) : FloatK (-coveBase T) ∧ (∀ n, stone (-coveBase T) n= -afterX (paste (intended p R)) 2) ∧ ∀ i,0 < i → (-coveBase T) i 2=0 := by
   let X:=coveBase T
   have he(n: Side): stone X n=afterX (paste (intended p R)) 2:= by
       ext1 e; rw [sow_coeff,sow,Finset.sum_eq_single (1+e)]
       · change facade _ (cum 0 n (if 0≤e ∧ (1+e)+0=1+e then T _ else 0))=_; rw [if_pos ⟨by omega,add_zero _⟩,ht _ n,beam_price,after_one,show 1+e+1=2+e by omega]
       · intro b _ hb; change facade _ (cum 0 n (if 0≤e ∧ b+0=1+e then T _ else 0))=0; rw [if_neg (by omega),cum_zero,map_zero]
       intro hi; rw [Finset.mem_range] at hi;omega
   have hx : FloatK X := by
       have hu: Vivid X := by
          have hx j: Agate (T j):= Matched.agate (h _) (hh _) (hv j).le (ht j) (fun i=>(strain _ _ hp (m:=i)).analytic)
          refine ⟨fun e r=>?_,fun e r=>?_,fun e r he=>?_⟩
          · cases r; exact up_zero 0; next r=> change Up (if _ then T r else 0); split; exact h r; exact up_zero _
          · cases r; exact agate_zero 0; next r=> change Agate (if _ then T r else 0);split;exact hx r;exact agate_zero _
          cases r; exact (he rfl).elim; next r=> change (if _ then T r else 0)≠0 at he; split at he <;> first|omega|contradiction
       refine {hu with fare:=fun i r=> ?_, civic:=fun n=>?_}
       · cases r
         · exact ⟨1,0,one_pos,bail_void ..⟩
         next r=> change ∃ η C:ℝ, 0<η ∧ Bail _ η (if 0 ≤ i ∧ r+0=1+i then T r else 0) C;split;exact ⟨_,_,hv _,hh _⟩;exact ⟨_,_,one_pos,bail_void _ 1 _⟩
       rw [he n]; intro s x I inst a b k ha hb hz hu H hk hv; have hp:=kernel_civic G n hp hS s x I _ _ _ ha hb hz hu H hk hv; rw [map_neg,map_neg] at hp; exact neg_inj.mp hp
   refine ⟨FloatN hx,fun n=> ?_,fun e he=>?_⟩
   · rw [books_neg hx,he]
   change -(if 0≤e ∧ 1+0=1+e then T 1 else 0)=0; rw [if_neg (by omega),neg_zero]

structure Troupe (T:Pot G)(p:Clip)(R:PathData G):Prop extends FloatK T where
    buys : ∀ n,stone T n=novel p R n
    seals: ∀ j,Sane T j
lemma manuscript (G:Gauge)(hG:G.Simple)(σ A Z:ℝ)(hp:0<σ)(hc:0≤A)(hz:0≤Z)(E:ℕ): ∃ δ K B:ℝ,0<δ ∧ 0≤ K ∧ 0≤ B ∧ ∀ p:Clip,p.direct≤ Z → ∀ (R:PathData G) Λ,R.Bounds p σ A Λ→ ∃ T:Pot G, Troupe T p R∧Fits T E δ (K+Λ*B):= by
    choose x C P Ho H using fun j=> main_money G σ A Z j hp hc hz
    obtain ⟨ζ,K,hζ,hK,h'⟩:=finance_family x C (1+E) P Ho
    obtain ⟨η,B,hη,hB,W⟩:= given_path G hp 1 E; let δ:=min ζ η;refine ⟨δ,K,B,lt_min hζ hη,hK,hB,fun p he R Λ H' => ?_⟩
    choose T hT b hx using fun i=> H i p R Λ he H'
    obtain ⟨hu,HX,hx2⟩:= book_caps H' hx hT P b hG
    obtain ⟨V,Y,k⟩:= W 2 (by decide) (by decide) R.loop Λ ⟨H'.two,fun i=>(H'.invariant i).1⟩
    let S:= -coveBase T; let q:= FloatN Y.toFloatK
    refine ⟨S+-V, ⟨float_plus hu q,fun n=> ?_,fun j i e h hp=>?_⟩,?_⟩
    · rw [booksK hu q,HX,novel,books_neg Y.toFloatK,Y.mountain n]
      rw [mountain,after_rope]; abel
      intro i hi; apply uncut_moans _ ⟨H'.two,fun j=>(H'.invariant j).1⟩ H'.width i hi
    · change value i ((-coveBase T) e 2+ -(V e 2))=0; rw [hx2 e hp,zero_add,←neg_one_smul ℝ, value_coin]
      by_cases hz:e=2
      · rw [hz,loop_budget H' Y i,mul_zero]
      have hb: V e 2=0:= by by_contra H; have he:= Y.lives _ _ H;omega
      rw [hb]; simp [value,mir,net,hem]
    apply Fits.add (T:= S) _ (Fits.mono (show Fits (-V) E η (Λ*B) from ⟨k.money,fun e h i=> (k.pay e h i).neg⟩) (min_le_right ..) le_rfl)
    refine ⟨hK,fun e he r=>?_⟩; cases r; exact (show Bail _ δ _ K from ((bail_void (V:=edgeL G) _ δ 0).mono hK).neg)
    next r=> change Bail _ δ (-(if 0≤e ∧ r+0=1+e then T r else 0)) K;split
             next hr=>exact ((b r).neg.shrink ((min_le_left ..).trans (h' r (by omega)).1)).mono ((h' r (by omega)).2)
             rw [neg_zero]; exact (bail_void ..).mono hK
end YM.FormalBulk08.Hay
