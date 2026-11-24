import YM.FVA2.O.Seam.Taxes
/-!
# Splitting the real log-scale axis for proof of estimates

`Way`: including transfer of estimates. Use to earn `Tame` on the union
of the lower and middle time ranges from bounds adapted to each (`season`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo Job.Belt
open scoped Topology ContDiff Interval
variable { α β E F I :Type } { G:Gauge } { S:Home α I } { T:Home β I }{P:Geo I}{F H:Glade G I} {n:ℕ}
variable { φ: α→ β}{x:β→ℝ} {a:α→ℝ}{b:ℤ}
structure Way (S:Home α I)(T:Home β I)(φ:α→ β) : Prop where
    owner i: T.pick (φ i)= S.pick i
    clock i: T.t ( φ i ) = S.t i
    basic i: T.basic (φ i)=S.basic i
namespace Way
variable ( h:Way S T φ )
include h
lemma length (i:α): T.length (φ i)=S.length i:= by rw [ ← T.slot, ← S.slot, h.clock ]
lemma bus : Bus S.toScale T.toScale φ:= ⟨ ⟨1,zero_lt_one,1,fun i=>by simp only [ Function.comp_apply,h.basic,pow_one,one_mul,mul_one,Pi.one_apply]; rfl ⟩,1,zero_lt_one,fun i=>by rw [h.length,one_mul] ⟩
lemma tags (H:I→ℝ→ E)(i:α): sendT T H (φ i)= sendT S H i:= by rw [sendT,h.owner, h.clock ]
lemma prices : (tar T P b)∘ φ= tar S P b:= by funext i; rw [Function.comp_apply,tar,h.owner, h.clock ]; rfl
lemma chart (F:Glade G I)[ NormedAddCommGroup E ][NormedSpace ℝ E] (w:Wire (BH G) E QP)(i:α): Chart (sendT S F) w i= Chart (sendT T F) w (φ i):= by funext p; unfold Chart; rw [h.tags]
lemma travels [NormedAddCommGroup E][NormedSpace ℝ E](w:Wire (BH G) E QP)(hp:Cape T.toScale (sendT T F) x w)(ha: nn a)(hx: x∘φ=a): Cape S.toScale (sendT S F) a w:= by
    subst a; unfold Cape; rw [ funext ( h.chart F w ) ]; refine ticket h.bus hp (paidMono fun i=>?_ ) ( fun i=>mul_nonneg ( length_p (S:=S.toScale) _ _ ) (ha i) ); dsimp only [Function.comp_apply]; rw [h.length]
lemma lease (hp:Latch.Lease false false T.toScale (sendT T F) x)(ht:nn a)(hx:x ∘ φ=a): Latch.Lease false false S.toScale (sendT S F) a:= fun E _ _ w he ht'=> h.travels w (hp E w he ht') ht hx
lemma cheap [NormedAddCommGroup E](p:E)(i:α): T.toScale.full.cheap ( φ i ) p=S.toScale.full.cheap i p:= by simp only [ Scale.full,Scale.weight,h.length,h.basic]
lemma tax (hp:totalT T F x false)(hx:x∘φ=a): totalT S F a false:= by
    intro E _ _ w hE; obtain ⟨C,hC,k,hp⟩:= hp E w hE; subst a; refine ⟨C,hC,k,fun i p _=>?_⟩; specialize hp (φ i) p trivial; dsimp only [ Qbud ] at *; rw [← h.chart F w i,h.cheap p, h.length] at hp; exact hp
lemma tiny (ht:Tiny T P F): Tiny S P F:= fun i=> h.tax (ht i) h.prices
end Way
abbrev Litt (P:Geo I): Home (Below P).time I := {
    toScale:= Lower P,pick:= Sigma.fst,t:= tstart, slot i:= ( coldE P i ).symm }
abbrev Mid (P: Geo I): Home (Gulf P).time I:={
    toScale:= (Gulf P).price,pick:= Sigma.fst,t:= tstart,slot _:= rfl }
local notation "M0"=> Mid P
local notation "L0"=> Litt P
local notation "B0"=> deckB P
lemma Litt.grass : Grass L0 P:= fun i=>le_trans ( i.2.property ) ( P.room _ )
lemma Mid.grass : Grass M0 P:= fun i=> i.2.property.2
lemma Belt_grass : Grass B0 P:= fun i=> i.2.property
lemma Mid.live : liveP M0 P.η:= fun i=> P.LightY _ _ _ i
lemma Litt.live : liveP L0 P.η:= fun i=> P.LightY _ _ _ i
abbrev leveling (i:( Gulf P ).time) : (Station P).Inst := (Station P).choose i.1 (tstart i) i.2.property.1
lemma Mid.way : Way M0 (face (Station P)) leveling:= by
    refine ⟨fun i=>rfl,fun i=>rfl,fun i=>?_ ⟩; change habitat P i.1 * (1+tstart i)= habitat P i.1 * (1+|tstart i|); rw [ abs_of_nonneg ( show 0≤tstart i from i.2.property.1 ) ]
lemma synchronized : Shy P F↔ Tiny B0 P F:= by
    have he(k:ℕ): tar B0 P k=bare_age (P:=P) k:= by funext i; unfold tar; rw [ Int.cast_natCast ]
    constructor; exact fun i=> Tiny.spec (fun k=>by unfold Pays; rw [he]; exact i k ) Belt_grass; exact fun i k=> ( he k ) ▸ ( show totalT B0 F _ false from i k )
lemma switch (ht:Pays L0 P F b)(hp:Pays M0 P F b): Pays B0 P F b:= by
    intro E _ _ w he; obtain ⟨C,hC,k,h⟩:= ht E w he; obtain ⟨D,hD,u,hp⟩:= hp E w he; refine ⟨ C+D,add_pos hC hD,k+u,fun s p _=>?_⟩; let v:=tstart s; have hv:= ( deckB P ).toScale.full.one_le s p trivial; have hT:0≤Qbud w (deckB P).toScale ( tar (deckB P) P b ) s:= pos_nn ( tar ( deckB P ) P b ) tar_nn ( deckB P ).toScale s; rcases le_total v 0 with he|he
    · let i:(Below P).time:= ⟨s.1,v,he⟩; apply le_trans ( h i p trivial ); change C*(( deckB P ).toScale.full.cheap s p)^k * Qbud w (deckB P).toScale (tar ( deckB P ) P b) s≤_; gcongr <;> linarith
    let i:( Gulf P ).time:= ⟨ s.1,v,⟨he, s.2.property ⟩ ⟩; apply le_trans ( hp i p trivial ); change D*(( deckB P ).toScale.full.cheap s p)^u*Qbud w (deckB P).toScale (tar (deckB P) P b) s≤_; gcongr <;> linarith
lemma Tiny.section (hp:Tiny L0 P F)(ht:Tiny M0 P F): Tiny B0 P F:= fun i=> switch (hp i) (ht i)
lemma season (ht:Tame L0 P F)(hp:Tame M0 P F): Tame B0 P F := by obtain ⟨q,h⟩:=ht; obtain ⟨b,hp⟩:=hp; exact ⟨ min q b, switch (Pays.size h Litt.grass (min_le_left ..)) (Pays.size hp Mid.grass (min_le_right ..))⟩
end YM.FVA2.O.Seam
