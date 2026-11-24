import YM.OPE.Compatible.Oasis.Loom
/-! # stage ready Tally. Trigger by α.B budgets -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set Finset Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
open Lass Lass.Zest
open Source Labels
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}{k k' m:ℕ}{T:Stage}
variable {n:I→Side} {A:Labels.Frame G k}{Q:∀ i, Rep G (n i)}{P:∀i,A.Coeff → Coefficient A (n i)}{H:Hol G}{S:SectionData A}
variable {β v:I→ℝ}{l:Filter I}(h:Tendsto β l atTop)
variable (P₁:∀ i,Torch S H 0 (Q i) (P i) m (salary (β i)))
variable (W:∀ᶠ i in l,Tag T (β i) (Q i).p (Q i).beta)(ht:∀ᶠ i in l,Grant (P₁ i) T)
include h W ht
lemma ClockFee : Torch.BondS P₁ β l (fun i=> gap (Q i).beta):=by
        let p:T.columns ≥ 1:= T.columns_ge
        refine ⟨flowers h _ W, ?_,ψsalary h _,ht.mono (fun i hi=> hi.a.symm ▸ (zero_le_one.trans p)), ?_,?_,?_ ⟩
        · exact (ΥPay h T.price_pos (-(11/10))).congr (W.mono fun i hi=> (by dsimp only [Ξoff]; rw[hi.width,hi.epoch]))
        · exact (Score.steady T.columns (carth h)).congr (ht.mono fun i hi=>hi.a.symm)
        · exact (Score.steady T.columns (carth h)).congr (ht.mono fun i hi=>hi.c.symm)
        exact (fieldReading A S h).congr (ht.mono fun i hi=> congr_arg (fun x:ℕ=>(x:ℝ)) hi.hue.symm)
omit W ht
variable {V Q Β A E:I→ℝ}
variable (hx:Tendsto V l atTop)(hg:RateIs l (Counters β) V 1)
variable (hf:∀ᶠ i in l,Q i ∈ Icc (β i/2) (2*β i))(hs:∀ᶠ i in l,E i ∈ Icc (V i/2) (2*V i))
variable (hE:∀ᶠ i in l,θj (V i)^2*|E i-Q i - A i|≤t*ℰb (V i)) (ht':RateLE l (Counters β) A 0)
-- bookkeeper sizes
include h hx hf hs hg ht' hE
lemma ClockAmp : Cameo.Quench (Counters β) l Q E A (fun i=>gap (Q i)) (fun i=>gap (E i)):=by
        let Vt:= Counters β; have hX:= carth hx; have hY:=carth h; have hy:=(boothP hf).Ray h; have hb:=(boothP hf).track h; have hm:=(boothP hs).Ray hx; have hC:=(boothP hs).track hx; have hF:RateIs l Vt E 1:= fScale2 hY hX hg.rate hm; refine ⟨hY,ht', fScale2 hY (carth hb) hy.rate (bread hb), fScale2 hY (carth hC) hF.rate (bread hC), ?_, ?_⟩
        · refine foTest h hg ?_; let zV:= Counters V; let H(i):= θj (V i); have hp:RateLE l zV (fun i=> t*ℰb (V i) / H i^ (2:ℕ)) (-(1/10)):=by
                 simp_rw [div_eq_mul_inv]; refine (((RateLE.const t hX).mul (Φmask hx)).mul (((edgeθ hx).power 2 |>.inv).pays hX)).mono (by norm_num)
          refine hp.of_norm_le ?_; filter_upwards [hE,(edgeθ hx).pos] with i hi h; exact (le_div_iff₀ (pow_pos h _)).2 (mul_comm ..|>.trans_le hi)
        filter_upwards [hy.pos,hF.pos] with i hi he; exact ⟨βδ hi,βδ he⟩
end YM.OPE.CardinalQ
