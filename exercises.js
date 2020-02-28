var cookies = document.cookie
var exercise_list = ['exercise1', 'exercise2', 'exercise3', 'exercise4', 'exercise5', 'exercise6', 'exercise7', 'exercise8', 'exercise9', 'exercise10', 'exercise11', 'exercise12', 'exercise13']
if (cookies) {
    var states = document.querySelectorAll('.exercise-state')
    var exercises = document.querySelectorAll('.exercise')
    for (var i = 0; i < exercise_list.length; i++) {
        setExercise(exercise_list[i], states, i, exercises)
    }
    
} else {
    for (var i = 0; i < exercise_list.length; i++) {
        setCookie(exercise_list[i], '0', 7)
    }
    var states = document.querySelectorAll('.exercise-state')
    var exercises = document.querySelectorAll('.exercise')
    for (var i = 0; i < states.length; i++) {
        states[i].textContent = '/ Not Completed'
        exercises[i].style = 'background:white'
    }
}

function setCookie(name,value,days) {
    var expires = "";
    if (days) {
        var date = new Date();
        date.setTime(date.getTime() + (days*24*60*60*1000));
        expires = "; expires=" + date.toUTCString();
    }
    document.cookie = name + "=" + (value || "")  + expires + "; path=/";
}
function getCookie(name) {
    var nameEQ = name + "=";
    var ca = document.cookie.split(';');
    for(var i=0;i < ca.length;i++) {
        var c = ca[i];
        while (c.charAt(0)==' ') c = c.substring(1,c.length);
        if (c.indexOf(nameEQ) == 0) return c.substring(nameEQ.length,c.length);
    }
    return null;
}

function setExercise(exerciseStr, states, counter, exercises) {
    var exercise = getCookie(exerciseStr)
    if (exercise == '1') {
        states[counter].textContent = '/ Completed'
        exercises[counter].style = 'background:lightgreen'
    } else {
        states[counter].textContent = '/ Not Completed'
        exercises[counter].style = 'background:white'
    }
}