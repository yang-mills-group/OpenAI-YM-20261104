import YM.OPE.Backup.Shades
import YM.OPE.Backup.Karat
/-! # Keep physical branch under gathering

Keeps all forced receipts (not just by being close to a resplicing).
Use any designated subset of singleton fibers. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster
open Function Filter Lattice RG Wilson Pressure Marker MeasureTheory
open Source Accent Menu Ribbon Extra.Multi Push Push.GridApprox.Nil Local
open Extra.Histories Extra.Trajectories Motion Merge PhysicalNext.Repeat Lotus
open MergeProof.Float OPE.Backup Finset
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n:Side}{R:Rep G n}
local notation "X"=> Names V I
local notation "Y"=> Names V J
-- Repricing hull invariant
set_option quotPrecheck false
variable (A:Fibers I J) (s:Finset J)
local notation "A'"=>partialGroup V A
local notation "Ξ"=> (Names V J).fire

def crew (V:Type)[Fintype V](s:Finset J): Finset (V×J):=univ×ˢ s
-- keep crew definition avoids decEq assumption? prod shadow
variable (L:Fibers.Salt (V×J) (V×I) (partialGroup V A) G n)
    {C: V×I→ℂ}{q:Config G n→ Poly (Names V I)}
    {o:V×I→Site n}{v:V}{g:V×I→ Config G n→ℂ}{k:V×I→ℕ→ Config G n→ℂ}
    {P:V→Motion}{E:V→Site n}{B:V→ Equiv.Perm V}{t:ℝ}
local notation "Z"=> (A').twig
lemma members (x:V×J) : x∈ crew V s ↔ x.snd∈s:= by simp [crew]
lemma crewed (h:∀ i ∈ s,A.Solo i) (i : V×J)(hi:i∈crew V s) : (A').Solo i:=by
   intro k hk; exact Prod.ext (congr_arg Prod.fst hk|>.symm) (h i.snd ((members ..).mp hi) k.snd (congr_arg Prod.snd hk))
lemma peppered (hr:∀ i,L.pepper i= if A.bunch i.2 ∈ s then 0 else C i)(h:∀ i∈s,A.Solo i)
    (hh:L.Breeze R.p.threshold)(he: q= Accent.play R X L.river (fun U=> Mach X C+∑ i,L.air i U)) (U:Config G n): Fibers.reap (A') (q U)=Accent.play R Y (L.soil R.p.threshold) (fun U=> Mach Y (fun i=> if i.2∈s then C (Z i) else 0)+∑ i,L.mount R.p.threshold i U) U:=by
   let T i:= if (A').bunch i ∈ crew V s then C i else 0; let C'(i:V×J):= if i.2∈s then C (Z i) else 0
   have hp: C= fun i=> T i + L.pepper i:=by
      funext i; rw [hr]; unfold T; simp only [members,partialGroup]; split_ifs <;> simp
   let τ:= R.p.threshold; let f:=L.income R; let H:= L.income R; let f' U := Accent.play R (Names V J) (L.soil τ) (fun U=> ∑ i,L.mount τ i U) U
   have hz(a b:V×I→ℂ): Mach X (fun i=>a i+b i)= Mach X a+Mach X b:=by unfold Mach; simp_rw [Extra.Trajectories.send_add,sum_add_distrib]
   let E₁:= Mach X T; let E₂:= Mach X L.pepper; let E' U:= ∑ i,L.air i U
   have he': q U=Poly.pass E₁*H U:= by
       nth_rw 1 [he]; unfold play; rw [hp,hz]; dsimp only; rw [add_assoc]; change (Real.exp _ : ℂ) • (Poly.pass (E₁+(E₂+E' U))* field _ _) = _; rw [pass_add (mute X T) (show (E₂+E' U).part (X|>.quiet) = 0 from ?_)]; change _ • _=Poly.pass E₁*((Real.exp _ : ℂ) • (_*_)); rw [mul_smul_comm,mul_assoc];
       unfold E' E₂; rw [Poly.part_plus,Poly.part_sum,mute,zero_add]; exact sum_eq_zero fun j _=> (hh.home j).sil U
   have hl (i:Support n):Burns L.focus i (L.mount τ i) τ:= (L.vessel τ).clearBurn τ (L.wet _ hh) (L.turn _ hh) _
   rw [he', Fibers.Deck.Token.passengers C (crew V s) (crewed A s h),show (Fibers.reap (A')) (H U) = f' U from ?_ ]; swap
   · unfold f' play H Fibers.Salt.income play; rw [map_smul,L.yields τ U hh] -- fix repeated
   rw [show (fun i=> if i∈crew V s then C (Z i) else 0)=C' from funext fun i=>by unfold C'; simp only [members]]
   let s':=∑ i,L.mount τ i U
   change Poly.pass _ * ((Real.exp _ : ℂ) • (Poly.pass s' * _))= _ • (Poly.pass (Mach _ C'+s')*_)
   rw [pass_add (mute Y C') (show s'.part (Y|>.quiet)=0 from ?_),mul_smul_comm, mul_assoc]; unfold s'; rw [Poly.part_sum]; exact sum_eq_zero fun j _=> (hl j).sil U
-- Pepper not present on NEW composite markers. special packaging.
variable {A s} {w:V×I→ℝ}{δ x t y a d b:ℝ}
local notation "τ"=> R.p.threshold
local notation "Θ" => R.p.supportExponent
lemma hook_blank (i:Box n)(U:Config G n) : hook R.activities R.p.threshold 0 i U=0:=by simp [hook]
lemma carefree {e:ℝ} (h:0 ≤ e) {o:V×J→Site n} {W:V×J→ℝ}: Garnish (G:=G) R.p o 0 W b e :=by
    refine ⟨fun _ _=> Local.Attaches.zero ..,fun i _ hh=> (hh rfl).elim,fun i=>?_⟩; refine ⟨0,fun j=>⟨le_rfl,fun U=>?_⟩,?_⟩ <;> simp [h]

def gyro (C:V×I→ℂ) (A:Fibers I J)(s:Finset J) (i:V×J):ℂ:= if i.2∈s then C ((partialGroup V A).twig i) else 0

lemma lodging {L:Fibers.Salt (V×J) (V×I) (partialGroup V A) G n}
    (hr:∀ i,L.pepper i=if A.bunch i.2∈s then 0 else C i)(hs:∀ i∈s,A.Solo i)
    -- EDIT placeholders
    (h:L.Breeze R.p.threshold) (hL:L.grain = o)
    (hf: q=Accent.play R X L.river (fun U=>Mach X C+∑ i,L.air i U))
    (hH:Horn v P E B L.air L.river)
    {F:V×J→ℕ→ Config G n→ℂ}{W:V×J→ℝ}{ψ: V×I→Response G n}
    (hh:∀ j,j≠v→ ∀ i:I, L.grain (j,i)=affine (P j).1 (E j) (L.grain (v,i)) ∧ C (j,i)=scalar (P j) (C (v,i)))
    (hc: L.Birth (L.income R) F W R d)
    (hy: Towed W id (L.mount τ) R.p.B Θ d)
    (ht: Towed W Prod.fst (L.soil τ) R.p.B Θ t)
    (hω : ∀ i U,(L.river i U).part (X|>.quiet)=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)
    (hM: May v P E B g (fun i=> profile R.activities (k i)) C)
    (hS: Garnish R.p o ψ w (Θ+1) δ) (hP: relates v P E ψ) (hρ:∀ i j U,(L.river i U).part ((Names V I).fire j)+hook R.activities R.p.threshold (ψ j) i U=profile R.activities (k j) i U)
    (hf':∀ j U,(q U).part (X|>.fire j)=coin R (g j) (k j) U)(hk:∀ j,Dominated (k j))(he:∀ i∈ crew V s,W i ≤ w (Z i))(hx:0 ≤ δ)(hW:∀ i,0 ≤ W i) (hV:R.activities.Valid R.p a b) :
      let F'(i:V×J):= if i.2∈s then g (Z i) else L.debt τ i
      let K'(i: V×J):= if i.2∈s then k (Z i) else F i
      Arc R F' K' (fun U=>Fibers.reap A' (q U)) v P E B (o ∘ Z) W Θ Θ d t δ (gyro C A s) ∧ May v P E B F' (fun i=>profile R.activities (K' i)) (gyro C A s) ∧ (∀ j,Dominated (K' j)) ∧ ∀ i U, (Fibers.reap A' (q U)).part (Y|>.fire i) = coin R (F' i) (K' i) U:=by
    let ψ'(i:V×J):= if i.snd∈s then ψ (Z i) else 0
    let F₀:= L.mount τ; let K₀:= L.soil τ; let o':= o ∘ Z; let t(i:V×J):= profile R.activities (k (Z i)); let f':= L.debt τ
    intro F' K'
    have hV'(i:V)(hi:i≠v): Fibers.CopyFamily L τ (P i) (E i) (district v J) (district i J) (nome (B i)) (nome (B i)):=
       by
          refine familyOf L ⟨fun _=>rfl,fun _=>rfl⟩ (hH i hi).1 (fun _=>Iff.rfl) (fun _=>Iff.rfl) (fun j=> ?_) (hH i hi).2 
          rw [hr,hr]; split; next h=> exact ⟨(hh _ hi j).1,(scalar_z _).symm⟩ 
          next h=> exact hh _ hi j
    -- fix copyfamily. hπ'
    have h': L.focus=o':= by unfold Fibers.Salt.focus; rw [hL]; rfl
    have hψ': Garnish R.p o' ψ' W Θ δ:=by
       have hψ : Garnish (G:=G) R.p o' 0 W Θ δ:= carefree hx; refine ⟨fun i p=>?_, fun i p ht=>?_, fun i=>?_⟩
       · unfold ψ'; split; exact hS.yes _ _; exact hψ.yes i p
       · unfold ψ' at ht; split at ht; exact hS.tracks _ _ ht; exact (ht rfl).elim
       unfold ψ'; split; next hp=>
          obtain ⟨y,hy,hY⟩:=hS.fee (Z i)
          refine ⟨y,hy, (sum_le_sum (fun j _=> ?_)).trans hY⟩; have hz : W i ≤ w (Z i):=he _ ((members ..).mpr hp); have hk:=hW i; have hy':= (hy j).1; have hr:=mul_nonneg hk hy'; gcongr <;> first| exact hW _| exact (hy _).1| linarith only
       exact hψ.fee _
    have hφ(i): Dominated (K' i):=by unfold K'; split; exact hk _; exact (hc.foot _).1
    have hT(i U): (K₀ i U).part (Y|>.quiet)=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U:=(L.taxed τ U h i).trans (hω i U)
    have hx (i:V×J)(U:Config G n) : (Fibers.reap (A') (q U)).part (Ξ i)=coin R (F' i) (K' i) U:=by
       by_cases hp:i∈crew V s
       · let y:=Z i; have ht:= (crewed _ s hs i hp).fire; change (q U).part (A'|>.plena _) = _; unfold F' K'; rw [ht,if_pos ((members ..).mp hp),if_pos ((members ..).mp hp), hf']
       have hs : i.2 ∉ s:= mt (members ..|>.2) hp
       have hl(i:Support n): Burns L.focus i (L.mount τ i) τ:=(L.vessel τ).clearBurn τ (L.wet _ h) (L.turn _ h) _
       rw [peppered A s L hr ‹∀ i∈s,A.Solo i› h hf]; let z(U):= Mach Y (gyro C A s)+ ∑ j,L.mount τ j U; let z' (U):= z U; change (Accent.play R Y K₀ z U).part _=_
       have hm:(z U).part (Y|>.quiet) = 0:=by unfold z; rw [Poly.part_plus,mute,Poly.part_sum,zero_add]; exact sum_eq_zero (fun j _=> (hl j).sil U)
       rw [beach R Y K₀ z U K' hV (fun i=>hT i U) hm i ((hφ _).summable U) (fun j=>by unfold K'; rw [if_neg hs]; exact hc.costs ..)]; unfold coin; rw [show F' i=f' i from if_neg hs]; change _* ((z U).part (Ξ i))+_= _*(L.debt τ i U)+_; rw [show (z U).part (Ξ i)= L.debt τ i U from ?_]; unfold z Fibers.Salt.debt; rw [Poly.part_plus,Accent.sing,gyro,if_neg hs,Poly.part_plus,Accent.sing]; rfl
    refine ⟨⟨F₀,K₀,ψ',hψ',?_,hy,ht,?_,?_,?_,hT,?_,funext fun U=>peppered A s L hr hs h hf U⟩,?_,hφ,hx⟩
    · intro i he j; unfold ψ'; split; next he'=> exact hP i he (A.twig j)
      next he' => funext j U; change 0= _; exact (scalar_z _).symm
    · intro j; change Burns o' _ (F₀ _) _; rw [← h']; exact (L.vessel τ).clearBurn τ (L.wet _ h) (L.turn _ h) _
    · intro j; change Flow o' _ (K₀ _) _; rw [← h']; exact (L.vessel τ).cloudy τ (L.wet _ h) (L.turn _ h) _
    · refine fun i hi=>⟨(hH i hi).1,fun U=> ?_⟩; have hh(s:(Names V J).Mode)(hz:Focused v s):= (hV' i hi).twines U s ((district_iff ..).2 hz); exact ⟨fun j p hs=> (hh p hs).1 j,fun j p hs=>(hh p hs).2 j⟩
    · intro i j U; unfold K' ψ'; split; next hp=>
          change (L.soil τ _ _).part _+_=_; have he : j∈crew V s:=(members ..).mpr hp
          rw [L.soil_preserves _ h (crewed _ s hs j he)]; exact hρ i (Z j) U
          rw [hr]; exact if_pos ((show A.bunch (Z j).2=j.snd from A.sectioned _) ▸ hp)
      next hp => rw [hook_blank,add_zero]; exact hc.costs ..
    intro i hi; have hh:= hV' i hi; refine ⟨(hH i hi).1,fun j=>?_⟩
    unfold F' K' gyro; by_cases hz:j∈s; · simp only [hz,if_true]; exact (hM i hi).2 (A.twig j)
    have ht:= hc.travels hh (show (v,j)∈district v J from rfl); rw [show nome (B i) (v,j)=(i,j) from Prod.ext (hH i hi).1 rfl] at ht; simp only [hz, ↓reduceIte, scalar_z]; exact ⟨ht.1,ht.2,trivial⟩
end YM.MergeProof.Ribbons.ManyCopies.Muster
