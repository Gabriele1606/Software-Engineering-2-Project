
open util/boolean

sig PowerStation{
}

sig Position{
longitude:Int,
latitude:Int
}

sig Payment{
id: one Int,
date:Int,
amount:Int,
discount:Int,
time:Int
}
{
amount>0
}



sig Ipad{
imei:one ImeiCode
}

sig ImeiCode{
}

sig Area{
park:some SafePark,
id:Int,
status:Bool
}

sig LicencePlate{
}

sig Vehicle{
	licence:one LicencePlate,
	position:one Position,
	carstatus:one CarStatus,
	system: one Ipad
}

sig PersonalData{
 licence: Int,
 name: one UserName,
 surname: one UserSurname,
 fiscalCode: one UserFiscalCode,
 birth:Int,
 idCard: Int,
 country: one UserCountry,
 region: one UserRegion,
 address: one UserAddress,
 city: one UserCity,
 sex: Bool
}

sig UserName{}
sig UserSurname{}
sig UserFiscalCode{}
sig UserCountry{}
sig UserRegion{}
sig UserAddress{}
sig UserCity{}

sig User{
	email:one UserEmail,
	password:one UserPassword,
	personalData:one PersonalData,
	position:one Position
}

sig UserEmail{
}
sig UserPassword{
}

sig Ride{
id: one Int,
startTime:Int,
date:Int,
endTime:Int,
distance:Int,
guestsNumber: Int,
startPosition: one Position,
status: one Bool,
endPosition: lone Position
}

sig Reservation{
timeexceeded: one Bool,
user:one User,
pinCode: Int,
id: one IdReservation,
date:Int,
time: Int,
vehicle: one Vehicle,
payment: lone Payment,
ride: lone Ride
}

sig IdReservation{
}



sig SafePark{
	id:one IdSafePark,
	status:one Bool,
	powerStation:lone PowerStation,
	position:one Position
}

sig IdSafePark{
}

fact paymentAssigned{
all pay:Payment| pay in Reservation.payment
}

fact rideAssigned{
all rid:Ride| rid in Reservation.ride
}

fact safeParkInArea{
all sp:SafePark| sp in Area.park
}

fact exclusivePark{
all v1: Vehicle |v1.carstatus=park implies (v1.carstatus!=break&&v1.carstatus!=charging&&v1.carstatus!=drive&&v1.carstatus!=fault)
}


fact exclusiveBreak{
all v1: Vehicle |v1.carstatus=break implies (v1.carstatus!=park&&v1.carstatus!=charging&&v1.carstatus!=drive&&v1.carstatus!=fault)
}


fact exclusiveCharging{
all v1: Vehicle |v1.carstatus=charging implies (v1.carstatus!=park&&v1.carstatus!=break&&v1.carstatus!=drive&&v1.carstatus!=fault)}

fact exclusiveFault{
all v1: Vehicle |v1.carstatus=fault implies (v1.carstatus!=park&&v1.carstatus!=break&&v1.carstatus!=drive&&v1.carstatus!=charging)}


fact exclusiveDrive{
all v1: Vehicle |v1.carstatus=drive implies (v1.carstatus!=park&&v1.carstatus!=break&&v1.carstatus!=charging&&v1.carstatus!=fault)}


fact numberOfGuests{
 all r1:Ride |(r1.guestsNumber>=1 && r1.guestsNumber<=4)
}

fact parkAreaAtLeastaPowerStation {
all a1:Area|#a1.park.powerStation>0
}

fact numberOfPassengers {
all r1:Ride | (r1.guestsNumber>=1 && r1.guestsNumber<=4)
}

fact ExistPaymentAfterRide{
all r1:Reservation| ((r1.ride.status in False) iff (#r1.payment =1))
}

fact carUniqueIdentified{
no disjoint v1,v2:Vehicle | v1.licence=v2.licence
}

fact timeExcededRule{
all res:Reservation| (res.timeexceeded in True) implies (#res.ride=0)
}

fact noMoreCarAtOneTime{
no r1, r2:Reservation| (r1.user=r2.user) && (r1!=r2 )&& (r1.ride.status in True) && (r1.ride.status in True)
}

pred Ride.existPayment[]{
 this.status in False
}

fact noCarDrivenByMoreUsers{
no v1:Vehicle,r1,r2:Reservation| r1!=r2 && r1.vehicle=v1 && r2.vehicle=v1 && r1.ride.status in True && r2.ride.status in True
}

assert noCarMoreUser{
no r1,r2:Reservation| r1!=r2 && r1.vehicle=r2.vehicle && r1.ride.status in True && r2.ride.status in True
}

fact noParkSamePos{
all p1, p2:SafePark|(p1!=p2) implies (p1.position!=p2.position)
}

fact exclusivePaymentReservation{
no pay1:Payment,r1,r2:Reservation| r1!=r2 && r1.payment=pay1 && r2.payment=pay1
}

fact exclusiveRideReservation{
no ride1:Ride,r1,r2:Reservation| r1!=r2 && r1.ride=ride1 && r2.ride=ride1 
}

fact timeExceededImpliesPayment{
all res1:Reservation| (res1.timeexceeded in True) iff (res1.ride=none && res1.payment!=none)
}

pred Reservation.carInUse{
this.ride.status.isTrue&&this.ride!=none
}

pred Reservation.isExpired{
this.timeexceeded in False && this.ride=none
}

assert noPayIfNotRideAndTimeexceededFalse{
all res1:Reservation|res1.isExpired implies res1.payment= none
}

assert rideStatusTrueImpliesNotPayment{
all res1:Reservation| res1.carInUse implies res1.payment = none
}

fact carParkedImpliesSafeParkOcuupied{
all v1:Vehicle, p1:SafePark| (v1.carstatus!=drive && v1.position=p1.position && v1.carstatus!= none && v1.position!= none && p1.position!= none) implies (p1.status in False)
}

fact noMoreOneimeiForIpad{
no ipad1, ipad2:Ipad|ipad1.imei=ipad2.imei &&ipad1!=ipad2&&ipad1!=none&&ipad2!=none
}

fact noMoreOneIpadForCar{
no v1, v2:Vehicle|v1.system=v2.system &&v1!=v2&&v1!=none&&v2!=none
}

fact ipadAssigned{
all ipad:Ipad| ipad in Vehicle.system
}

enum CarStatus{park, break, charging,drive,fault}

pred show(){
Reservation.payment=none
}
check rideStatusTrueImpliesNotPayment
check noPayIfNotRideAndTimeexceededFalse
check noCarMoreUser
run show for 3
