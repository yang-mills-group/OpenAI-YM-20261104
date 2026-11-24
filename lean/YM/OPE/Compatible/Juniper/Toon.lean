import YM.OPE.Compatible.Juniper.Vow
/-! # transfer residual heavy to all tested moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
local notation "Fλ"=> fieldX (Shade G)
section
variable [NormedAddCommGroup E][NormedSpace ℝ E]
lemma sectorJ (p q:E→ℝ)(v:JetS E)(hp:ContDiff ℝ (↑(2:ℕ)) p)(hq:ContDiff ℝ (↑(2:ℕ)) q): Jpiece v (p+q)= Jpiece v p+Jpiece v q:=by
       have hh (i:Phase) : (Jpiece v (p+q)).seq i.val=(Jpiece v p).seq i.val+(Jpiece v q).seq i.val:=by
             rw[← brightX v (show ContDiff ℝ 2 (p+q) from hp.add hq),← brightX v hp,← brightX v hq]; unfold WardBin.leading; have hn: ContDiff ℝ (↑i.val:ℕ∞ω) v.atK := (kernelS v).of_le le_top; have hb:i.val≤2:=by have h:=i.isLt;omega
             rw[show (p+q)∘ v.atK=p ∘ v.atK+q ∘ v.atK from rfl,iteratedDeriv_add ((hp.of_le (Nat.cast_le.mpr hb)).comp hn|>.contDiffAt) (((hq.of_le (Nat.cast_le.mpr hb)).comp hn).contDiffAt),smul_add]
       exact JetS.eta _ _ (hh 0) (hh 1) (hh 2)
abbrev hitch (a:E)(p:E→ℝ):=Stranded.pointD a p
variable (L:E→L[ℝ] Vec G n 1)[FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
structure GuardB (μ:Measure E)(A:Law E)(e k:ℕ)(p:E→ℝ):Prop where
       hW : Stature p e
       block : Haven μ A k p
namespace GuardB
variable {μ A}{a b:E→ℝ}{i j k z:ℕ}
omit [μ.IsAddHaarMeasure][BorelSpace E][FiniteDimensional ℝ E] in lemma skids (h:GuardB μ A i j a)(hk:k ≤ i)(hz:z ≤ j):GuardB μ A k z a:=⟨h.hW.mono hk,h.block.points hz⟩
lemma splices (h:GuardB μ A i j a)(he:GuardB μ A i j b):GuardB μ A i j (a+b):=by
       refine ⟨h.hW.add he.hW,⟨fun {k} hv x hx=>?_⟩⟩; have hX:= Stature.poly hx.cost i; rw [add_mul,duneAdd A μ (runsG _ _ (h.hW.mul hX)) (runsG _ _ (he.hW.mul hX)),h.block.bill hv _ hx,he.block.bill hv _ hx,add_zero]
omit [BorelSpace E][μ.IsAddHaarMeasure] in
lemma stomp (h:GuardB μ A i j a)(he:anthem k b)(hz:z+k ≤ j): GuardB μ A i z (a*b):=⟨h.hW.mul (Stature.poly he.cost i),h.block.cohabit he hz⟩
lemma totBeam (s:Finset X) (p:X→E→ℝ)(h:∀ x∈s,GuardB μ A i j (p x)): GuardB μ A i j fun a=>∑ x∈s,p x a:=by
       induction s using Finset.induction_on with
       | empty=> simp only [Finset.sum_empty]; refine ⟨Stature.poly (Bond.keep 0) _,⟨fun he q h=>?_⟩⟩; rw [show (fun _ : E=> (0:ℝ))*q=0 from zero_mul _]; exact singleConst μ A 0
       | insert i s hi ih=> simp_rw[sum_insert hi]; exact (h i (mem_insert_self ..)).splices (ih fun j hj=>h j (mem_insert_of_mem hj))
end GuardB
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma flumes (b:ℕ) (x:E): (BFilm b (Charu o L x)).s = floss G b o (L x):=by
       rw [BFilm_s]; unfold floss; change strideG G b (liftP b (ascJ o (L x)))= strideG G b (socket b (InLine _ (ascJ o (L x)))); rw[homeB]
lemma gun {f:Scoop G b→ℝ}(hv:Sensor A μ (floss G b o ∘L L) f r):GuardB μ A r (r+1) (f ∘ (floss G b o ∘L L)):=⟨hv.stays.blot _,hv.toHaven A μ _⟩ -- arg order
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma bill_one {I:Type}[Fintype I] [DecidableEq I] (x:PAD I)(p: PAD I→ℝ)(v:PAD I): hitch x p v=∑ i:I,hitch (Pi.single i 1) p v*x i:=by
       change fderiv ℝ _ _ _=_; nth_rw 1 [show x=∑ i,x i • (Pi.single i 1:PAD I) from funext fun i=>by simp [Pi.single_apply,Finset.sum_apply]]; rw [_root_.map_sum]; exact Finset.sum_congr rfl fun i _=> (_root_.map_smul (fderiv ℝ _ _) _ _).trans (mul_comm ..)
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma bits_I {I:Type}[Fintype I] [DecidableEq I](x: PAD I)(p: PAD I→ℝ)(v:PAD I)(h:ContDiff ℝ 2 p): hitch x (hitch x p) v=∑ i:I, ∑ j:I,hitch (Pi.single i 1) (hitch (Pi.single j 1) p) v*(x i*x j):=by
       have he(i j): hitch i (hitch j p) v= iteratedFDeriv ℝ 2 p v (Fin.cons j (fun _=>i)):=by rw [Analysis.cons_inner (by exact_mod_cast h.contDiffAt),iteratedFDeriv_one_apply]; rfl
       simp_rw[he]; let T:=iteratedFDeriv ℝ 2 p v; have hs(i:PAD I): (fun _:Fin 1=>i)=Fin.cons i (fun _:Fin 0=>0):=funext fun j=> by fin_cases j ;rfl
       simp_rw [hs,← ContinuousMultilinearMap.curryLeft_apply]; rw [brewC,brewC T,_root_.sum_apply]; apply sum_congr rfl; intro i hi; simp only [_root_.smul_apply]; simp_rw [ContinuousMultilinearMap.curryLeft_apply]; rw [_root_.sum_apply]; simp_rw[smul_eq_mul, mul_sum,_root_.smul_apply,smul_eq_mul]; exact Finset.sum_congr rfl fun i _=>by ring_nf; rw[ContinuousMultilinearMap.curryLeft_apply]; congr! 6
local notation "D!"=> Fpaper G b
local notation "ZX"=>floss G b o
omit [MeasurableSpace E] [BorelSpace E] in lemma Clippy (j:ℕ)(a:Fpaper G b): anthem j (fun i:E=> PlateB j b (Charu o L i) a):=vim o L (pealB a)
lemma Turn_S (u:ℕ)(f:Scoop G b→ℝ) (h:Sensor A μ (floss G b o ∘L L) f (u+6))(i:Phase): GuardB μ A (u+6-(i.val)) (u+7-3*i.val) (fun y:E=> (Autum f (Charu o L y)).seq i.val):=by
      let X:=f; let V(y):=Charu o L y; let B(y):= BFilm b (V y); let T:=floss G b o ∘L L; have hz(y):(B y).s=T y:= flumes ..
      let q (j:ℕ)(y:E):=PlateB j b (V y); have hv (i j): anthem i (fun y:E=> q i y j):= Clippy ..
      have hp(r:ℕ)(e z:ℕ)(p:Scoop G b→ℝ)(hp:Sensor A μ T p (z+1))(ht:e+r≤ z+1):GuardB μ A z e (fun y:E=>hitch (q r y) p (T y)):=by
           rw[funext (show ∀ y:E, hitch (q r y) p (T y)= _ from fun y=>bill_one (q r y) p (T y))]; let u(i:D!):= (fun y:E=>hitch (Pi.single i 1) p (T y)) * (fun y:E=>q r y i); change GuardB μ A z e fun x:E=>∑ i,u i x; apply GuardB.totBeam (s:=Finset.univ) (p:=u); intro i _; exact GuardB.stomp (gun (f:=(hitch (Pi.single i 1) p)) o L μ A (Sensor.pick _ _ _ hp (Pi.single i 1))) (hv _ _) ht -- pick order
      have hy:BorelSpace E:=inferInstance; fin_cases i
      · change GuardB μ A (u+6-(0:Phase).val) (u+7) (fun y=> f ((B y).s)); simp_rw [hz]; exact gun o L μ A h
      · change GuardB μ A (u+6-(1:Phase).val) (u+7-3*1) (fun y=>hitch (q 2 y) f ((B y).s)); simp_rw [hz]; exact hp 2 _ (u+5) f h (by omega)
      let Z(y:E):= hitch (q 2 y) (hitch (q 2 y) f) ((B y).s); change GuardB μ A (u+6-2) (u+7-3*2) (fun y=> hitch (q 3 y) f ((B y).s)+1/2*Z y);
      have he : GuardB μ A (u+6-2) (u+7-3*2) Z:=by
           let p(i j:D!):= hitch (Pi.single i 1) (hitch (Pi.single j 1) f); let g(i j:D!)(y:E):= p i j (T y)* (q 2 y i*q 2 y j); rw [show Z=fun y:E=>∑ i:D!,∑ j:D!,g i j y from ?_]; apply GuardB.totBeam (p:=fun i y=>∑ j:D!,g i j y); intro i _; apply GuardB.totBeam; intro j _; have hh: Sensor A μ T (p i j) (u+4):= (Sensor.pick A μ T (p:=(hitch (Pi.single j 1) f)) (Sensor.pick A μ T h _) (Pi.single i 1)) -- format; pick rank mismatch
           exact (gun o L μ A hh).skids (k:=u+6-2) (by omega) le_rfl |>.stomp (z:=u+7-3*2) ((hv 2 i).times (hv 2 j)) (by omega) -- r parm
           funext y; unfold Z; rw [hz,bits_I (q 2 y) f (T y) (by exact (h.stays.smooth.of_le (by exact_mod_cast (show 2 ≤ u+6 by omega))))]
      have hw: GuardB μ A (u+6-2) (u+7-3*2) (fun y=>1/2* Z y):=by
           rw [funext (show ∀ y:E,1/2*Z y=Z y*(1/2) from fun _=> mul_comm ..)]; exact he.stomp (anthem.bank 0 _) (by omega)
      simp_rw [hz]; exact (hp 3 _ (u+5) f h (by omega)).skids (by omega) (le_refl (u+7-3*2))|>.splices hw
end
end YM.OPE.Spells
