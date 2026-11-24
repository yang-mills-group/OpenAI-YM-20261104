import YM.ForFlash.MS.Quote
import YM.ForFlash.F9.Oven
import YM.SignedWilsonExpansion.F9.TollQ

/-! # Pose paid on that epoch

Geometry readouts corresponding to `Purchase/FacetClock.poseStamp`
and `Minty.art` (and still use the original version on other compact jobs in
this Epoch). Bring all the layout up to the shifted position in Top native
epoch, including Ward supports, mirrors, looked at the summit of a suitable
full integral mesh. Retains arities. -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission.TollQ
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Asymptotics
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Mer.Xa.MarqueQ
variable {G:Gauge}{n d:ℕ}{ι:Type} {L:Filter ι}
variable (H : G.Simple) (W':Initialize G){P':Normalize.Store G}(K:Rose.Pick P')
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (S : Prescription (Press.portDeck G))
variable (ν:ℝ) (M:Speed.Quoted W' K T S) (x:ι→ Sample n) (p:ι→ Stage n)

structure SeatsForFlash (L:Filter ι)(x:ι→ Sample n)(p:ι→ Stage n):Prop where
    paid : Speed.WideForFlash L x
    align : ∀ᶠ i in L,familiar (x i)=(p i).val

include ν H M
lemma priceForFlash (sx:SeatsForFlash L x p)(D:Tags G d n)(k:ℕ) :
    (fun i=> (Rose.measureₓ W' K d (x i) k D) - Measure.start W' K d n ( p i ) k D)=O[L] (Speed.chip ∘ grab ∘ x) ∧
    (fun i=> Measure.start W' K d n (p i) k D)=O[L] (1:ι→ℝ):=by
    obtain ⟨hp,hr,hv⟩:= M.toContract.toMission.born
    have ht:= Speed.paymentForFlash ν W' K S T H hp hr hv D (k:=k) sx.paid
    have hq:(fun i=> Reg.Faith.rate ν K T d (familiar (x i)) k D)=ᶠ[L] fun i=> Measure.start W' K d n (p i) k D:= by
        filter_upwards [ sx.align ] with i hi; rw [hi,tuner H W' K T S ν M]
    exact ⟨ht.sails.congr' ((EventuallyEq.rfl (f:=fun i=>Rose.measureₓ W' K d (x i) k D)).sub hq) (.refl ..),ht.quote.congr' hq (.refl ..)⟩ -- projections syntax .congr'
end YM.SignedWilsonExpansion.Commission.TollQ

namespace YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense Ticket Cosmos Cosmos.Polestar Source
open MarqueQ Method PorchK Epic Stair FVA2 FVA2.Scale Cooking
open scoped Topology Classical BigOperators
variable {G:Gauge}{M:Levels G}{e n h d k u K:ℕ}{ι:Type}
variable {T:Initialize G} {R:Realm G (e+1) Credit.leanC}{F:Labels.Frames G}{Ω:Council F}
open WardBin
variable {ρ B Y U U' ε N:ι→ℝ} {l m c b v r w P':ι→ℕ}{L:Filter ι}
variable (p:∀ i,0<ρ i)(Q:∀ h,Rays G h T.hol) (Z:ι→ PorchK T F Q Ω R h k u) (H':Yonder Q R L m b v c r l U p Z B)
variable (f:Rise B L)
local notation "S₀"=> (fun i=> roof R.draws (l i) (c i) (ρ i) (p i))
variable (he:Stretched L (fun i=> roof R.draws (l i) (c i) (ρ i) (p i))) (Room: RoomForFlash R L B l c ρ p T Q F h k)
include p f he Room
set_option maxHeartbeats 390000 in
lemma artForFlash (hw:l ≤ᶠ[L] c)(y:ι→ Stage n)(h':P'≤ᶠ[L] c)(x:ι→Fin n→ Cover)(u:MovesIn L B (fun i=>Garden (hereD R.draws ρ P' i) (x i)))(p':∀ᶠ i in L,(y i).val= Garden (hereD R.draws ρ P' i) (x i)) :TollQ.SeatsForFlash L (picture l c P' x R.draws p) y:=by
    let s:=picture l c P' x R.draws p
    let a0 (i:ι):=hereD R.draws ρ P' i; let a₁(i:ι):= hereD R.draws ρ c i
    have hf:= alignedChart p R.draws hw h' x
    obtain ⟨a,d,hA,hD,hz⟩:= u.places
    obtain ⟨b,hb,hh⟩:= Room.spacing
    obtain ⟨nc, hn⟩:= exists_nat_gt (a/b); rw [div_lt_iff₀ hb] at hn
    refine ⟨⟨he,d,1,nc,hD,zero_le_one,?_⟩, (hf.and p').mono fun i hi=>hi.1.trans hi.2.symm⟩
    filter_upwards [hf,hz, hh, payD_fee f hn.le] with i hi hv h1 hB
    refine InWidth.fitsForFlash (d:=d) _ (position _) (?_)
    rw [hi,one_mul]; apply hv.more le_rfl; refine hB.trans ?_
    change payD B (nc*b) i≤ ( a₁ i )⁻¹ ^ nc; unfold a₁
    rw [payD_pow, Pi.pow_apply]; gcongr
    apply le_trans _ (inv_anti₀ (sizeT_pos _ (p i) (c i)) h1); rw [payD_inv,Pi.inv_apply,inv_inv]

include H'
lemma hearthForFlash (t:h≤k)(x:ι→Fin (n+1)→ Cover)(p':MovesIn L B (fun i=>Garden (hereD R.draws ρ b i) (x i))) (X:ℝ): ∀ᶠ i in L, Regard (T.tree (orbitP R.draws.S (l i) (c i))) R (l i) (c i) (summit R.draws (l i)) F T.surveys Q h k ( pine R.draws.S (b i) (c i) (x i)) (payD B (-X) i):=by
    let y(i):=pine R.draws.S (b i) (c i) (x i); have hw:l≤ᶠ[L]c:= (H'.spectrum Q p Z).mono fun i ⟨_,p,q,w,t,r⟩=> t.trans (r.trans w); have hb:b≤ᶠ[L]c:= ( H'.spectrum Q p Z ).mono fun i ⟨_,_,p,h,_,_⟩=>p.trans h; let e:= p'.tee ( z:=fun i=>Garden (hereD R.draws ρ c i) (y i)) ( hb.mono fun i hi=> (stamp_pine _ _ (p i) hi).symm )
    filter_upwards [ Cape.pearlForFlash f p hw he Room.total Q F y e t,(Room.spread n y e).baked X ] with i hi hp using ( ⟨senior ..,hi,hp,pay_pos B _ _|>.le⟩ )

lemma poseStampForFlash (t:h≤k)(u₀:(n+1)*h≤u)(x:ι→Fin (n+1)→ Cover)(p':MovesIn L B (fun i=>Garden (hereD R.draws ρ b i) (x i)))(N:ι→ℕ)(hc:c ≤ᶠ[L] N): ∃ d:ℝ,0<d ∧ ∀ ε:ℝ, PoseW d Z (picture l c b x R.draws p) (shapeO b x R.draws) L (payD B (-ε)) N:=by
    obtain ⟨a,d,hA,hD,hp⟩:= p'.places; let s (i):= summit R.draws (l i); have hw:= H'.frame; have he':∀ᶠ i in L,b i≤ c i:= ( H'.spectrum Q p Z ).mono fun i ⟨_,_,p,h,_,_⟩=>p.trans h
    refine ⟨d,hD,fun e=> { align:= hw.mono fun i h=> h.2.2.2.2.2.2.2.2.symm, length:= (hw.and hc).mono fun i hi=> hi.1.2.2.2.1.trans_le hi.2, proper:=u₀,pos:=hD,enrolled:=?_ }⟩; filter_upwards [hw,he',hp, hearthForFlash p Q Z H' f he Room t x p' e ] with i ⟨a,b₀,d₀,c₀,r',l',ρ',z,hH⟩ hl hx hh; rw [b₀,c₀,ρ',l']; exact ⟨s i,fun _=>rfl,seating _ (p i) hl hD hx.charter (mem_singleton _) ,hh ⟩
end YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
end
