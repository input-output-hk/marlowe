/*!
 * jQuery event extension: jquery-elementresize 0.2.2, 2016-01-21, 09:02.
 * Description: Provides a custom jQuery event to detect resizing of a positioned (non-static) element.
 * Author: Robert Bar, robert@rbsoftware.pl, http://rbsoftware.pl 
 * License: MIT
 */
(function (factory) {
    'use strict';
    if (typeof define === 'function' && define.amd) {
        // AMD. Register as an anonymous module.
        define(['jquery'], factory);
    } else if (typeof exports === 'object') {
        // Node/CommonJS style for Browserify/Webpack
        module.exports = factory(require('jquery'));
    } else {
        // Browser globals
        factory(jQuery);
    }
}(function ($) {    
    'use strict';
    var specialEventName = 'elementResize';
    
    function ElementResizeDetector(elem) {
        this.elem = elem;
        this.$elem = $(elem);
        this.activate();
    }

    function addDetector(elem) {
        if (!$.data(elem, specialEventName)) {
            $.data(elem, specialEventName, new ElementResizeDetector(elem));
        }        
    }
    
    function removeDetector(elem) {
        var detector = $.data(elem, specialEventName);
        
        if (detector) {
            detector.destroy();
            $.removeData(elem, specialEventName);
        }            
    }    

    $.extend(ElementResizeDetector.prototype, {
        activate: function () {
            var frameContent = '<!DOCTYPE html><html><head><title>jquery.elementResize</title></head><body><script>window.onresize = resize;function resize() { var detector = parent.$ ? parent.$(this.frameElement).data("elementResize") : null; if (detector) { detector.trigger(); } }</script></body></html>',
                iframes = [
                    $('<iframe src="about:blank" style="position:absolute; top:-50000px; left:0px; width:100%;"></iframe>'), 
                    $('<iframe src="about:blank" style="position:absolute; top:0; left:-50000px; height:100%;"></iframe>') 
                ];

            for (var index = 0; index < iframes.length; index++) {
                var $iframe = iframes[index];            
                this.$elem.append($iframe);
                $iframe.data(specialEventName, this);
                $iframe[0].contentWindow.emitcontent = frameContent;
                /* jshint -W107 */
                $iframe[0].src = 'javascript:window.emitcontent';
                /* jshint +W107 */
            }

            this.iFrameArray = iframes;
        },        

        destroy: function() {  
            for (var index = 0; index < this.iFrameArray.length; index++) {
                var $iframe = this.iFrameArray[index];
                $iframe.removeData(specialEventName);
                $iframe.remove();
            }
            this.iFrameArray = null;
            this.$elem = null;
            this.elem = null;
        },

        trigger: function() {
            this.$elem.elementResize();
        }
    });
    
    $.event.special[specialEventName] = {              
        version: '0.2.0',
        
        setup: function() {
            if (this.nodeType === 1) {
                addDetector(this);
            } else {
                throw new Error('Unsupported node type: ' + this.nodeType);
            }
        },
        
        teardown: function() {
             removeDetector(this);
        }
    }; 
    
    $.fn.extend({
        elementResize: function(fn) {
            return fn ? this.bind(specialEventName, fn) : this.trigger(specialEventName);
        },
        
        unelementResize: function(fn) {
            return this.unbind(specialEventName, fn);
        }
    });

}));



